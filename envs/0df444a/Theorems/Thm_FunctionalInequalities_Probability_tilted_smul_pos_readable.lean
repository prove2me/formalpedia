-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_tilted_smul_pos_readable
-- name    : FunctionalInequalities.Probability.tilted_smul_pos_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:13.565129+00:00
-- url     : https://prove2.me/theorems/082bb7e7-9916-4a6e-aaa8-68ce8d9f378f
-- title:
--   Invariance of Normalized Tilts Under Positive Rescaling
-- statement:
--   This statement proves that normalized tilting is unchanged by a positive rescaling of the base measure.
--
--   Let $A$ be a measurable space, let $μ$ be a measure on $A$, let $f:A\to\mathbb R$, and let $c>0$. Using the definition `Measure.tilted`, the normalized tilt of $(\operatorname{ENNReal.ofReal}(c)\,\bullet\,μ)$ equals the normalized tilt of $μ$:
--
--   $$
--   (\operatorname{ENNReal.ofReal}(c)\,\bullet\,μ).\operatorname{tilted}(f)
--   =
--   μ.\operatorname{tilted}(f).
--   $$
--
--   This algebraic invariance isolates the normalization property of tilted measures and does not require probability or finiteness assumptions on $μ$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Probability.tilted_smul_pos {A : Type*} [MeasurableSpace A] (μ : Measure A)
--       (f : A → ℝ) {c : ℝ} (hc : 0 < c) :
--       (ENNReal.ofReal c • μ).tilted f = μ.tilted f
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564).
--
--   Next: [`Covariance.operator_map_continuousLinearEquiv`](https://prove2.me/theorems/4b0ba356-0a64-4912-a8f7-67b0e65a1329).
--
--   [Source excerpt, lines 55–57](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Transport.lean#L55-L57) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Transport.lean#L54-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Transport`, declaration `FunctionalInequalities.Probability.tilted_smul_pos`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport

open MeasureTheory Filter Topology InnerProductSpace
variable {A B : Type*}

theorem FunctionalInequalities.Probability.tilted_smul_pos_readable {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ) {c : ℝ} (hc : 0 < c) :
    (ENNReal.ofReal c • μ).tilted f = μ.tilted f := by sorry
