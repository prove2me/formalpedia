-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_leaf_joint_solve_exec
-- name    : NearlyOptimalPPR.Computation.leaf_joint_solve_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:37.400123+00:00
-- url     : https://prove2.me/theorems/2d1bb289-6f62-46d0-96b8-7d3f83c7574f
-- title:
--   Leaf high-set collection and exact joint solve with heap credit
-- statement:
--   Assume a represented recursive state with valid regions and keys, positive-degree stored active vertices, valid epoch marks, and sufficient queue capacity. Let $C$ be the nonempty union of the current cache and high-residual set, $h$ the top level, and
--
--   $$S=\operatorname{vol}(C)+|C|.$$
--
--   The leaf routine has a finite execution representing the source leaf-solve transition. It collects the high set, prepares the cache and right-hand side, performs the exact solve, and refreshes all touched records. Heap mass grows by at most $2(h+1)(|C|+S)$. With $P$ the cleaning coefficient, its charged work plus $PM'$ is bounded by initial work plus $PM$, the explicit leaf preparation/solve/refresh allowances, and one exact-solve charge. The output is preserved and the epoch advances by one.
--
--   The heap credit covers stale high entries during collection and prevents their repeated traversal from becoming uncharged work.
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
theorem leaf_joint_solve_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ) (epoch : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1) (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hNonempty : ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).Nonempty)
    (hDegree : ∀ v ∈ (logical.frames logical.top).cache ∪ (logical.frames logical.top).high,
      0<g.graph.degree v)
    (hEpoch : st.scalar.core.ptrs 53=epoch)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch)
    (hMass : pm.queueMass+2*(logical.top+1)*
      (((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card+
        (volumeNat g ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high)+
          ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card)) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
    let size := volumeNat g C+C.card
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let A := (C.card+1)*leafPreparationFactor ell logical.top length rank
    let B := leafSolveUnitCost ell logical.top rank C.card size
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (compilerLeafSolve m g α logical) out,
      MachineEval m g ω leafJointSolveCode st steps out ∧ steps ≤ P*pm.queueMass+A+B+1 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*(C.card+size) ∧
      out.work+((P*memory.queueMass : ℕ) : ℝ≥0∞) ≤
        st.work+((P*pm.queueMass+(A+B+P*(2*(logical.top+1)*size)) : ℕ) : ℝ≥0∞)+solveCharge m C.card size ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (out.scalar.core.ptrs 53=epoch+1 ∧ ∀ v : Fin n,
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch+1) := by sorry
end NearlyOptimalPPR.Computation
