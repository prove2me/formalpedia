-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_integrable_exp_sub_norm_readable
-- name    : FunctionalInequalities.Probability.integrable_exp_sub_norm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:02.968676+00:00
-- url     : https://prove2.me/theorems/6e84bf56-c441-4d85-881f-7cdd5b15ecb5
-- title:
--   Haar Integrability Of Exponential Norm Decay
-- statement:
--   This is a finite-dimensional Haar-integrability estimate for exponential norm decay.
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure, let $dx$ be an additive Haar measure on $E$, and let $c\in\mathbb R$ satisfy $c>0$. For every $M\in\mathbb R$,
--   $$y\longmapsto\exp(M-c\|y\|)$$
--   is integrable with respect to $dx$.
--
--   This supplies the integrable exponential envelope used in conjugate-mass estimates, including the zero-dimensional case.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_exp_sub_norm [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       (dx : Measure E) [dx.IsAddHaarMeasure] {c : ℝ} (hc : 0 < c) (M : ℝ) :
--       Integrable (fun y : E => Real.exp (M - c * ‖y‖)) dx
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/ConjugateMass`](https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f).
--
--   Next: [`limsup_density_legendre_le`](https://prove2.me/theorems/50c36fd7-1bb7-40be-8a5b-91f04f40fa30).
--
--   [Source excerpt, lines 36–38](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L36-L38) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L34-L60 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.integrable_exp_sub_norm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass

open MeasureTheory Filter Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Probability.integrable_exp_sub_norm_readable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (dx : Measure E) [dx.IsAddHaarMeasure] {c : ℝ} (hc : 0 < c) (M : ℝ) :
    Integrable (fun y : E => Real.exp (M - c * ‖y‖)) dx := by sorry
