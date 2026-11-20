-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_controller_source_step_exec
-- name    : NearlyOptimalPPR.Computation.controller_source_step_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:40.802865+00:00
-- url     : https://prove2.me/theorems/0a02741d-6594-413b-ac69-5580e952dc1a
-- title:
--   One compiled controller body simulates one recursive source step
-- statement:
--   Let a live logical state satisfy the recursive region, key, boundary, parameter, stored-vertex, and numerical invariants, and let a concrete controller memory represent it. Assume sufficient capacities for ordinary branches and valid queue rank and potential-credit parameters. The entire controller body, including prioritized component completion and ordinary dispatch, has a finite execution representing one canonical recursive source step. It satisfies
--
--   $$M'\le M+G_{\rm body},\qquad W'+\Phi'\le W+\Phi+\Delta_{\rm body}.$$
--
--   The symbols denote heap masses, the specified body growth, charged work, heap-and-cache potential, and the explicit body charge. In the component branch the output representation is completed; otherwise the returned representation is live.
--
--   This contract includes the operational component test, budget scans, program-counter lookup, and branch guards.
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
theorem controller_source_step_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q M : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hα : 0<α ∧ α<1)
    (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical) (hBoundary : BoundaryIdentity g logical)
    (hParameters : ParameterInvariant logical) (hStored : StoredInvariant g logical) (hNumerical : NumericalInvariant g logical)
    (hm : memory.mass ≤ M) (capacities : ¬componentComplete logical → ControllerCapacities g logical ell M N)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (recursiveStep m g s α ell [] logical) out,
      MachineEval m g ω controllerBodyCode st steps out ∧ next.mass ≤ M+controllerSourceGrowth g ell logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerBodyCharge m g logical ell length rank Q := by sorry
end NearlyOptimalPPR.Computation
