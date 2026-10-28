-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_interior_support_nonempty_of_eq_tilted_readable
-- name    : FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:15.923921+00:00
-- url     : https://prove2.me/theorems/f9e547f0-9041-4fe6-9d08-ab4991b4217f
-- title:
--   Tilted Haar Laws Have Full Support
-- statement:
--   This theorem states that a probability law obtained by tilting Haar measure has nonempty support interior.
--
--   Let $V$ be a measurable normed space, let $m$ be an additive Haar measure, let $\nu$ be a probability measure, and let $W:V\to\mathbb R$ satisfy
--
--   $$
--   \nu=m.\operatorname{tilted}(-W).
--   $$
--
--   Then
--
--   $$
--   \operatorname{interior}(\operatorname{supp}\nu)\ne\varnothing.
--   $$
--
--   In fact, the support is all of $V$ under the hypotheses in the type. This auxiliary fact is used to supply the nonempty-interior-support assumption required by the closed weighted-gradient constructions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem interior_support_nonempty_of_eq_tilted (m : Measure V) [m.IsAddHaarMeasure] {W : V → ℝ}
--       (hνW : (ν : Measure V) = m.tilted (-W)) :
--       (interior (ν : Measure V).support).Nonempty
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38).
--
--   Supporting theorems: [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70).
--
--   Previous: [`isBorellDensity_of_eq_tilted`](https://prove2.me/theorems/0d7194a7-857d-46cc-b91c-8366be9b61de) · Next: [`convexOn_of_eq_tilted`](https://prove2.me/theorems/c25e8adc-034c-4eda-8eb4-4a844cb9f0fc).
--
--   [Source excerpt, lines 152–154](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L152-L154) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L150-L169 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, declaration `FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V]

theorem FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted_readable (m : Measure V) [m.IsAddHaarMeasure] {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    (interior (ν : Measure V).support).Nonempty := by sorry
