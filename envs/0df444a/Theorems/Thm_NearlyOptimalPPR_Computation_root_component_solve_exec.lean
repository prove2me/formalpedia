-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_root_component_solve_exec
-- name    : NearlyOptimalPPR.Computation.root_component_solve_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:44.194551+00:00
-- url     : https://prove2.me/theorems/3cc5c3f1-1e3c-416b-8dff-2185201ffe6f
-- title:
--   Finite component-completion solve and explicit sparse output
-- statement:
--   Let the represented root active set $C$ be nonempty and consist of stored positive-degree vertices, with $0<\alpha<1$ and valid epoch marks. The root component-solve routine has a finite execution whose explicit output denotes
--
--   $$\alpha D M_C^{-1}e_s.$$
--
--   Here the inverse is the principal-domain solve extended by zero outside $C$. Writing $S=\operatorname{vol}(C)+|C|$, charged work is bounded by the explicit enumeration, sparse assembly, and emission allowance plus one exact-solve charge for dimension $|C|$ and sparse size $S$. The instruction count has the corresponding allowance plus one primitive call, and the machine remains ready to continue.
--
--   This implementation contract is used when the controller has already established component completion; it separately charges output emission.
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
theorem root_component_solve_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (epoch : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1) (hNonempty : (logical.frames 0).active.Nonempty)
    (hStored : (logical.frames 0).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames 0).active, 0<g.graph.degree v)
    (hEpoch : st.scalar.core.ptrs 53=epoch)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch) :
    let size := volumeNat g (logical.frames 0).active+(logical.frames 0).active.card
    let cost := (10*(logical.frames 0).active.card+5)+((24*(16*(ell+3))+100)*size+28)+
      ((4*(16*(ell+3))+21)*(logical.frames 0).active.card+6)+3
    ∃ steps out, MachineEval m g ω rootComponentSolveCode st steps out ∧ steps ≤ cost+1 ∧
      outputVector out.output=potentialOutput g.graph α (solveOn g α (logical.frames 0).active (LocalPush.e s)) ∧
      out.work ≤ st.work+(cost : ℕ)+solveCharge m (logical.frames 0).active.card size ∧ out.scalar.halted=false := by sorry
end NearlyOptimalPPR.Computation
