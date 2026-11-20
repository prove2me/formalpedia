-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_cached_principal_solve_memory_exec
-- name    : NearlyOptimalPPR.Computation.cached_principal_solve_memory_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:45:50.920858+00:00
-- url     : https://prove2.me/theorems/8b7871ec-d101-44b8-9c4a-912dbe6d20bf
-- title:
--   Sparse exact principal solve preserves recursive frames and produces owned answer buffers
-- statement:
--   Let $C$ be a nonempty injectively enumerated set of stored positive-degree vertices with $0<\alpha<1$ and a represented right-hand side $b$. Assume the enumeration is below the allocation frontier and disjoint from every owned frame, and that all index marks are bounded by the current epoch. Put
--
--   $$S=|C|+\sum_{v\in C}d_v.$$
--
--   The principal-solve routine has a finite execution that preserves the represented logical recursive state and its heap mass, builds owned enumeration/answer buffers, and stores the principal solution $M_C^{-1}b_C$ extended by zero outside $C$. With record width $w$, its instruction count is at most $(24w+100)S+29$, and its charged work is at most initial work plus $(24w+100)S+28$ and the exact-solve charge. Existing output is preserved. The epoch advances by one and all index marks remain bounded by it.
--
--   This theorem separates sparse numeric assembly and valid primitive invocation from later potential propagation and key refresh.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Algorithms 1 and 6–9, pp. 5,14–22; charged local-machine realization of the mission computational model.

import Definitions.Def_NearlyOptimalPPR_Computation_compiler_runtime
import Definitions.Def_NearlyOptimalPPR_Computation_compiler_buffers
open Finset Matrix
open scoped ENNReal
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace NearlyOptimalPPR.Computation
open SparseQueue
theorem cached_principal_solve_memory_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length offset : ℕ)
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
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch) :
    let capacity := k+∑ i : Fin k, (g.neighbors (e i)).length
    let answerBase := base+3*(capacity : ℤ)+(k : ℤ)
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω cachedPrincipalSolveCode st steps out ∧
      steps ≤ (24*(16*(ell+3))+100)*capacity+29 ∧
      SolveIterationBuffers memory enumBase answerBase e (solveOn g α (Finset.univ.image e) b) ∧
      memory.queueMass=pm.queueMass ∧ SolveBufferLayout out.scalar base k capacity ∧
      out.scalar.core.ptrs 80=enumBase ∧ out.scalar.core.ptrs 53=epoch+1 ∧
      out.work ≤ st.work+((24*(16*(ell+3))+100)*capacity+28 : ℕ)+solveCharge m k (principalEntries g α e).length ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch+1) := by sorry
end NearlyOptimalPPR.Computation
