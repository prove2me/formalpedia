-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_norm_vectorItoProcess_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_sq_norm_vectorItoProcess_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:07.442063+00:00
-- url     : https://prove2.me/theorems/4ad59ff0-71f2-424a-9d06-361263c34b7c
-- title:
--   Second Moment Bound for a Vector Itô-Process Increment
-- statement:
--   This is a second-moment estimate for the norm of a vector Itô-process increment.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $W$ be a $d$-dimensional Brownian motion with coordinate Brownian filtrations, and let $H_{mk}$ be measurable, progressively measurable integrands whose squared norms have finite extended integrals on every positive interval. Assume $C\ge0$ and $|H_{mk}(\omega,s)|\le C$. Let $X_0:\Omega\to\operatorname{Fin}(n)\to\mathbb R$ and let $b_m(\omega,s)$ be measurable drift coefficients. Assume that $B\ge0$ and $|b_m(\omega,s)|\le B$ for every $m,\omega,s$. For $0\le u<v$, consider `vectorItoProcess` built from these data.
--
--   The increment is square-integrable and
--   $$
--   \int_\Omega \left\|X_v(\omega)-X_u(\omega)\right\|^2\,dP(\omega)
--   \le n\left(2\bigl(B(v-u)\bigr)^2+2d^2C^2(v-u)\right).
--   $$
--
--   This provides the coordinate-to-vector second-moment estimate used in later window and grid bounds.
--
--   **Formalization Note** The norm is the norm on $\operatorname{Fin}(n)\to\mathbb R$, and all natural-number factors are coerced to $\mathbb R$. The conclusion also asserts integrability of the squared norm.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sq_norm_vectorItoProcess_sub_le {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
--       Integrable (fun ω => ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
--           - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 2) P
--         ∧ ∫ ω, ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
--             - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 2 ∂P
--           ≤ (n : ℝ) * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u))))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`integrable_abs_drift_pow`](https://prove2.me/theorems/a6288035-95df-498a-8432-a20089aba59f), [`integrable_sq_add_and_le`](https://prove2.me/theorems/84c68f33-8dc4-400b-b0e0-ff74d29b1e54), [`integral_sq_vectorItoMartingale_sub_le`](https://prove2.me/theorems/d36fc9ed-f7c1-4780-bf4d-334940405111), [`measurable_vectorItoProcess_sub`](https://prove2.me/theorems/a8a3a0c4-bf0d-4b14-81c4-23f97e4dcb97), [`abs_setIntegral_Ioc_le`](https://prove2.me/theorems/7eab41d0-09a0-484b-9388-f6640a71836d).
--
--   Previous: [`integral_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/8034fbf3-4cec-4cc1-8421-d12baf9f25de) · Next: [`integrable_norm_vectorItoProcess_sub_pow_three`](https://prove2.me/theorems/4ebc222e-11b8-4943-afb1-b14792258eba).
--
--   [Source excerpt, lines 494–499](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean#L494-L499) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L492-L539 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integral_sq_norm_vectorItoProcess_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
include hbm hC0 hCH hB0 hB

theorem LevyStochCalc.Brownian.Ito.integral_sq_norm_vectorItoProcess_sub_le_readable {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 2) P
      ∧ ∫ ω, ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 2 ∂P
        ≤ (n : ℝ) * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u)))) := by sorry
