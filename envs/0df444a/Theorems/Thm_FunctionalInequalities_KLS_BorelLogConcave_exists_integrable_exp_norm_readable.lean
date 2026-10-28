-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_readable
-- name    : FunctionalInequalities.KLS.BorelLogConcave.exists_integrable_exp_norm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:14.657024+00:00
-- url     : https://prove2.me/theorems/cae54259-25c9-4b6d-b8ab-140080dd2348
-- title:
--   Existence of an Exponential Norm Moment
-- statement:
--   This establishes an exponential moment for a Borel log-concave probability law.
--
--   Let $V$ be a real normed space with Borel measurable structure, and let $\nu$ be a `BorelLogConcave` probability measure on $V$. Then there exists $t>0$ such that
--
--   $$\int_V e^{t\lVert v\rVert}\,d\nu(v)<\infty.$$
--
--   Equivalently, the function $v\mapsto e^{t\lVert v\rVert}$ is integrable with respect to $\nu$. No finite-dimensionality assumption appears in the Lean type beyond the stated typeclass assumptions. This supplies exponential integrability for later moment arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BorelLogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_integrable_exp_norm {ν : ProbabilityMeasure V}
--       (hν : BorelLogConcave ν) :
--       ∃ t : ℝ, 0 < t ∧ Integrable (fun v ↦ Real.exp (t * ‖v‖)) (ν : Measure V)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/BorellRepresentation/Moments`](https://prove2.me/theorems/e5df2dc6-6ebd-4244-bfb5-41d46b1c70d1).
--
--   Definition modules: [`KLS/LogConcave/Borel`](https://prove2.me/theorems/d5735b5c-11b9-4f7a-9a4b-077472bdb999).
--
--   [Source excerpt, lines 112–114](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Moments.lean#L112-L114) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Moments.lean#L108-L193 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments`, declaration `FunctionalInequalities.KLS.BorelLogConcave.exists_integrable_exp_norm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments

open MeasureTheory Set Topology Filter
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V]

theorem FunctionalInequalities.KLS.BorelLogConcave.exists_integrable_exp_norm_readable {ν : ProbabilityMeasure V}
    (hν : BorelLogConcave ν) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun v ↦ Real.exp (t * ‖v‖)) (ν : Measure V) := by sorry
