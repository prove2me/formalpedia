-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_controller_pc_exec
-- name    : NearlyOptimalPPR.Computation.controller_pc_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:29.425126+00:00
-- url     : https://prove2.me/theorems/cb809468-2285-489c-b78f-ad8b0e7879fe
-- title:
--   All recursive program-counter cases implement their source transitions
-- statement:
--   Let a live logical recursive state satisfy the region, key, boundary, parameter, stored-vertex, and numerical invariants. Assume its controller memory representation, correct budget flags, sufficient branch capacities, and valid queue-rank and potential-credit parameters. The routine for its current program-counter case has a finite execution representing the corresponding source controller transition. For initial and final heap masses $M,M'$ and the specified allowed growth $G$,
--
--   $$M'\le M+G,\qquad W'+\Phi'\le W+\Phi+\Delta_{\rm pc}.$$
--
--   Here $W$ is charged machine work, $\Phi$ is the sum of heap-cleaning and cache credits, and $\Delta_{\rm pc}$ is the explicit charge for the selected case. All ten cases are covered, including normal/interrupted returns and budget-dependent branches.
--
--   The theorem composes executable primitive contracts; it does not assume accuracy, termination of the whole algorithm, or its desired total work bound.
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
theorem controller_pc_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q M : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hα : 0<α ∧ α<1)
    (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical) (hBoundary : BoundaryIdentity g logical)
    (hParameters : ParameterInvariant logical) (hStored : StoredInvariant g logical) (hNumerical : NumericalInvariant g logical)
    (hFlags : ControllerBudgetFlags logical st) (hm : memory.mass ≤ M)
    (capacities : ControllerCapacities g logical ell M N)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (controllerNext m g α ell logical) out,
      MachineEval m g ω (controllerPCCode (logical.frames logical.top).pc) st steps out ∧
      next.mass ≤ M+controllerStepGrowth g ell logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerPCCharge m g logical ell length rank Q := by sorry
end NearlyOptimalPPR.Computation
