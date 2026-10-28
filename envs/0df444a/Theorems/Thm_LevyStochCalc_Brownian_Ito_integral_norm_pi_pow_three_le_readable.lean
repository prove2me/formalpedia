-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_norm_pi_pow_three_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_norm_pi_pow_three_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:29.118994+00:00
-- url     : https://prove2.me/theorems/5d6166a6-3ea2-4998-af8d-3304ea548177
-- title:
--   Third Moment Bound for the Supremum Norm from Coordinates
-- statement:
--   This is a finite-dimensional norm estimate.
--
--   Let $x:\Omega\to(\operatorname{Fin}(n)\to\mathbb R)$ be measurable. Assume that each coordinate $|x(\cdot,p)|^3$ is integrable and that numbers $c_p\in\mathbb R$ satisfy
--   $$
--   \int_\Omega|x(\omega,p)|^3dP(\omega)\le c_p
--   $$
--   for every $p\in\operatorname{Fin}(n)$. Then
--   $$
--   \int_\Omega\|x(\omega)\|^3dP(\omega)
--   \le n^2\sum_{p<n}c_p.
--   $$
--
--   This lemma converts coordinatewise cubic estimates into a bound for the norm on $\operatorname{Fin}(n)\to\mathbb R$ and does not require $P$ to be a probability measure.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_norm_pi_pow_three_le {n : ℕ} {x : Ω → Fin n → ℝ} (hxm : Measurable x)
--       (h3 : ∀ p : Fin n, Integrable (fun ω => |x ω p| ^ 3) P) {c : Fin n → ℝ}
--       (hc : ∀ p : Fin n, ∫ ω, |x ω p| ^ 3 ∂P ≤ c p) :
--       ∫ ω, ‖x ω‖ ^ 3 ∂P ≤ (n : ℝ) ^ 2 * ∑ p, c p
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoThirdMoment`](https://prove2.me/theorems/a91256d3-896e-401f-8609-adb538add313).
--
--   Previous: [`integral_abs_sum_pow_three_le`](https://prove2.me/theorems/8e2176da-9942-4d76-ae35-887c676c9109) · Next: [`integral_abs_vectorItoMartingale_sub_pow_three_le`](https://prove2.me/theorems/e79302a4-4518-490f-9961-50ba76dc4c8d).
--
--   [Source excerpt, lines 69–72](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoThirdMoment.lean#L69-L72) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoThirdMoment.lean#L67-L88 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoThirdMoment`, declaration `LevyStochCalc.Brownian.Ito.integral_norm_pi_pow_three_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoThirdMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoThirdMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.integral_norm_pi_pow_three_le_readable {n : ℕ} {x : Ω → Fin n → ℝ} (hxm : Measurable x)
    (h3 : ∀ p : Fin n, Integrable (fun ω => |x ω p| ^ 3) P) {c : Fin n → ℝ}
    (hc : ∀ p : Fin n, ∫ ω, |x ω p| ^ 3 ∂P ≤ c p) :
    ∫ ω, ‖x ω‖ ^ 3 ∂P ≤ (n : ℝ) ^ 2 * ∑ p, c p := by sorry
