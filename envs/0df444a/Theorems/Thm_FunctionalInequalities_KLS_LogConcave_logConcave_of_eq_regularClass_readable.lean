-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_logConcave_of_eq_regularClass_readable
-- name    : FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_regularClass_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:32.931677+00:00
-- url     : https://prove2.me/theorems/a4ee60d4-3b28-491b-804e-e9c2455e28ed
-- title:
--   Log-Concavity of a Regular-Class Density
-- statement:
--   This statement proves log-concavity from a regular-class density representation.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $μ$ be a probability measure, and let $K\subseteq E$. Assume:
--
--   1. $K$ is closed and convex;
--   2. $W:E\to\mathbb R$ is continuous;
--   3. $κ>0$;
--   4. $y\mapsto W(y)-(κ/2)\|y\|^2$ is convex on $E$;
--   5. as measures,
--
--   $$
--   μ=\operatorname{volume}.\operatorname{withDensity}\!\left(1_K(x)\,\operatorname{ENNReal.ofReal}(e^{-W(x)})\right).
--   $$
--
--   Then `LogConcave μ` holds. This result converts the analytic regular-class description into the abstract log-concavity predicate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem logConcave_of_eq_regularClass
--       (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
--       {W : E → ℝ} (hW : Continuous W) {κ : ℝ} (hκ : 0 < κ)
--       (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
--       (hμ : (μ : Measure E) = (volume : Measure E).withDensity
--         (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
--       FunctionalInequalities.KLS.LogConcave μ
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`rpow_mul_rpow_le_of_convexOn`](https://prove2.me/theorems/60c904f9-1850-43a9-b676-71efcb52afb5).
--
--   Previous: [`convexOn_of_eq_tilted`](https://prove2.me/theorems/c25e8adc-034c-4eda-8eb4-4a844cb9f0fc).
--
--   [Source excerpt, lines 294–300](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L294-L300) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L294-L311 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, declaration `FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_regularClass`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_regularClass_readable
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : Continuous W) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    FunctionalInequalities.KLS.LogConcave μ := by sorry
