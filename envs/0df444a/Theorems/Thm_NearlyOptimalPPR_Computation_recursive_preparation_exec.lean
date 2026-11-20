-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_preparation_exec
-- name    : NearlyOptimalPPR.Computation.recursive_preparation_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:28.680984+00:00
-- url     : https://prove2.me/theorems/96ca2109-281e-43db-b01f-30572dfcf207
-- title:
--   Charged parameter preparation and sparse recursive-root initialization
-- statement:
--   Fix an integer amplification constant $B\ge1$ and an input with $0<\varepsilon\le1$, represented in the constant-size input layout with zero boundary counter. The recursive preparation routine has a finite execution. It computes the accessible depth $\ell$, root threshold $q$, scale $N$, and binary rank $r$, satisfying
--
--   $$8\le Nq,\qquad N\le8/q+1,\qquad 0<N<2^r,\qquad r\le\lfloor\log_2N\rfloor+1.$$
--
--   It initializes a complete sparse representation of the source root state with queue mass at most one, amplified rank-array length, zero solve epoch, and bounded epoch marks. All work equals its instruction count, bounded by the explicit charged search, header, and sparse-initialization formula in the interface. It performs exactly one graph query and preserves existing output.
--
--   The result charges all scalar parameter searches and initializes only the seed-dependent sparse state.
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
theorem recursive_preparation_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (B : ℕ) (hB : 1 ≤ B) (s : Fin n) (α ε : ℝ) (hε : 0<ε) (hε1 : ε ≤ 1)
    (st : MachineState) (hh : st.scalar.halted=false) (input : PushInputMemory s α ε st)
    (hBoundary : st.scalar.integerMemory 7=0) :
    let ell := accessibleDepth (1/ε)
    let q := rootThreshold ε ell
    ∃ (N r steps : ℕ) (out : MachineState), ∃ memory : RecursiveMachineMemory g s α ε ell (amplifiedQueueRank B r+1)
      (recursiveInit g s q ell []) out,
      MachineEval m g ω (recursivePreparationCode B) st steps out ∧
      8 ≤ (N : ℝ)*q ∧ (N : ℝ) ≤ 8/q+1 ∧ 0<N ∧ N < 2^r ∧ r ≤ Nat.log 2 N+1 ∧
      steps ≤ (12*(ell+2)^3+4*N+4*r+24)+(B+14)+
        (12*(16*(ell+3))+64+(⌈1/q⌉₊+2)*(4*ell+22)+10*(amplifiedQueueRank B r+1)+264+
          (21*(amplifiedQueueRank B r)+60*(16*(ell+3))+190)) ∧
      memory.queueMass ≤ 1 ∧ out.scalar.core.ptrs 150=0 ∧ out.scalar.core.ptrs 151=1 ∧
      out.scalar.core.ptrs 53=0 ∧ EpochInvariant (n:=n) (16*(ell+3)) out ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries+1 ∧ out.output=st.output ∧ out.scalar.halted=false := by sorry
end NearlyOptimalPPR.Computation
