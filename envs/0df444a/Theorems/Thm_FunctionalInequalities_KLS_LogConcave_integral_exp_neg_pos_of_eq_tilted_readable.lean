-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_exp_neg_pos_of_eq_tilted_readable
-- name    : FunctionalInequalities.KLS.LogConcave.integral_exp_neg_pos_of_eq_tilted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:26.838794+00:00
-- url     : https://prove2.me/theorems/fb765bf9-81da-4922-b614-0b50e7223f1c
-- title:
--   Positive Normalizing Integral for a Probability Tilt
-- statement:
--   This is a positivity statement for a tilted probability law.
--
--   Let $V$ be a measurable space, let $\nu$ be a probability measure on $V$, let $m$ be a measure on $V$, and let $W:V\to\mathbb R$. Assume that $\nu=m.\mathrm{tilted}(-W)$ as measures. Then the normalizing integral is strictly positive:
--
--   $$0<\int_V e^{-W(x)}\,dm(x).$$
--
--   The result is a basic normalization fact used when identifying densities of tilted probability measures; it does not require norm, inner-product, finite-dimensional, or Borel-space structure.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_exp_neg_pos_of_eq_tilted {m : Measure V} {W : V → ℝ}
--       (hνW : (ν : Measure V) = m.tilted (-W)) :
--       0 < ∫ x, Real.exp (-W x) ∂m
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38).
--
--   Supporting theorems: [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70).
--
--   Previous: [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70) · Next: [`rpow_mul_rpow_le_of_convexOn`](https://prove2.me/theorems/60c904f9-1850-43a9-b676-71efcb52afb5).
--
--   [Source excerpt, lines 49–51](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L49-L51) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L47-L72 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, declaration `FunctionalInequalities.KLS.LogConcave.integral_exp_neg_pos_of_eq_tilted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V]

theorem FunctionalInequalities.KLS.LogConcave.integral_exp_neg_pos_of_eq_tilted_readable {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    0 < ∫ x, Real.exp (-W x) ∂m := by sorry
