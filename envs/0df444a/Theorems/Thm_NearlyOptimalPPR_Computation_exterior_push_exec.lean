-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_exterior_push_exec
-- name    : NearlyOptimalPPR.Computation.exterior_push_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:35.394805+00:00
-- url     : https://prove2.me/theorems/c3400010-75f8-4bbf-aea4-d057acd921dc
-- title:
--   Exterior push faithfully updates all open recursive frames
-- statement:
--   Fix an exterior vertex $v$ at a recursion level $j$ in the domain of a represented logical state. Assume the active/cache domain conditions, represented selection and boundary count, nonnegative next boundary count, valid next-state keys, and sufficient queue capacity. Let $h$ be the top level and $d_v$ the queried degree. The exterior-push routine has a finite execution representing exactly the source exterior-push transition, including its activation branch, with
--
--   $$M'\le M+2(h+1)(d_v+1).$$
--
--   Its instruction count is at most the explicit exterior-push bound determined by the record width, top level, queue rank, and $d_v$. Charged work increases by exactly that instruction count. The routine preserves the output and every solve-epoch mark and retains the selected vertex in the designated register.
--
--   The contract includes stored adjacency, residual propagation, activation and boundary bookkeeping, and restoration of the open ancestor representations.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Algorithms 1 and 6–9, pp. 5,14–22; charged local-machine realization of the mission computational model.

import Definitions.Def_NearlyOptimalPPR_Computation_compiler_runtime
open Finset Matrix
open scoped ENNReal
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace NearlyOptimalPPR.Computation
open SparseQueue
theorem exterior_push_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank t boundary : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t) (hvNot : v ∉ (logical.frames t).active)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hCacheDomain : ∀ i ≤ logical.top, (logical.frames i).cache ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ)) (hBoundaryNext : 0 ≤ (exteriorPush g α logical t v).boundaryEdges)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (exteriorPush g α logical t v) out,
      MachineEval m g ω exteriorPushProgramCode st steps out ∧
      steps ≤ exteriorPushBound ell logical.top rank (g.neighbors v).length ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ w : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)) := by sorry
end NearlyOptimalPPR.Computation
