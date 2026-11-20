-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_cached_joint_solve_exec
-- name    : NearlyOptimalPPR.Computation.cached_joint_solve_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:34.087255+00:00
-- url     : https://prove2.me/theorems/50822d51-7797-4c84-9efd-e88c85d2b3bd
-- title:
--   Cached sparse joint solve implements the recursive potential update
-- statement:
--   Let $C$ be a nonempty injectively enumerated set of stored positive-degree vertices, let $b$ be a represented right-hand side, and assume $0<\alpha<1$. Suppose the sparse enumeration lies below the allocation frontier, is disjoint from owned frame objects, and the recursive keys, domains, epoch marks, and queue-capacity conditions hold. Write
--
--   $$S=\operatorname{vol}(C)+|C|,\qquad y=M_C^{-1}b_C.$$
--
--   The cached-solve routine has a finite execution that represents the logical joint update by $y$, followed by key refresh on all touched vertices. Its heap mass increases by at most $2(h+1)S$, where $h$ is the top recursion level. Scalar work is bounded by the explicit assembly and refresh costs in the interface; the exact-solve charge is added separately. It preserves the existing output and advances the solve epoch by one, bounding every stored index mark by the new epoch.
--
--   This contract accounts for assembly, the valid exact primitive, potential propagation, and key restoration as one reusable operation.
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
theorem cached_joint_solve_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank offset : ℕ)
    (base enumBase epoch : ℤ) (hEnumBase : 0 ≤ enumBase)
    (e : Fin k → Fin n) (he : Function.Injective e) (hk : 0<k) (hd : ∀ i, 0<g.graph.degree (e i))
    (hα : 0<α ∧ α<1) (b : Fin n → ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hmem : ∀ j, e j ∈ logical.stored) (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hEnumBelow : ∀ i : Fin k, enumBase+(i.val : ℤ) < base)
    (hForeign : ∀ i : Fin k, ∀ j, ∀ hj : j ≤ logical.top, enumBase+(i.val : ℤ) ∉ (pm.frames j hj).owned)
    (hb : st.scalar.core.ptrs 80=enumBase) (hkp : st.scalar.core.ptrs 77=(k : ℤ))
    (hf : st.scalar.core.ptrs 20=base) (hE : st.scalar.core.ptrs 53=epoch)
    (hOff : st.scalar.core.ptrs 83=(offset : ℤ))
    (hbRecords : ∀ i : Fin k, st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) (e i).val offset)=b (e i))
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch)
    (hKeys : KeysInvariant g logical)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hMass : pm.queueMass+2*(logical.top+1)*(volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let size := volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card
    let numericCost := (24*(16*(ell+3))+100)*size+28
    let updateCost := jointSolveIterationFactor ell logical.top rank*size+5
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (refreshKeys g (jointUpdate g α logical (solveOn g α (Finset.univ.image e) b)) (touchedBy g (Finset.univ.image e))) out,
      MachineEval m g ω cachedJointSolveCode st steps out ∧
      steps ≤ numericCost+updateCost+1 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*size ∧
      out.work ≤ st.work+(numericCost+updateCost : ℕ)+solveCharge m k (principalEntries g α e).length ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (out.scalar.core.ptrs 53=epoch+1 ∧ ∀ v : Fin n,
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch+1) := by sorry
end NearlyOptimalPPR.Computation
