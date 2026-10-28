-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_itoFormula_of_unbounded_coeff_readable
-- name    : LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded_coeff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:27.506378+00:00
-- url     : https://prove2.me/theorems/26b3bb9f-845f-407e-8e95-6d9fce1413b9
-- title:
--   Itô Formula with Unbounded Coefficients
-- statement:
--   Let $X$ be a vector Itô process with measurable, progressively measurable, square-integrable diffusion coefficients $H$ and drift $b$, and assume the filtration, null-set, initial-value, and integrability hypotheses in the declaration. Let $f$ have first and second Fréchet derivatives $f',f''$, with bounded norms $K_1,K_2$, continuous derivatives, and the stated uniform continuity condition on $f''$. Then for every $T>0$, almost surely,
--
--   $$
--    f(X_T)-f(X_0)
--   =\sum_p\int_{(0,T]}\partial_p f'(X_s)b_p(s)\,ds
--   +\sum_{p,k}\int_0^T\partial_p f'(X_s)H_{pk}(s)\,dW_s^k
--   +\frac12\sum_{p,q}\int_{(0,T]}\partial_{pq}f''(X_s)\sum_kH_{pk}(s)H_{qk}(s)\,ds.
--   $$
--
--   The formal conclusion is an almost-everywhere equality of real-valued functions and retains the explicit volume integrals and stochastic-integral hypotheses.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--         fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
--       (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {T : ℝ} (hT : 0 < T) :
--       (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
--         (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
--             coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
--           + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
--               (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
--               (hmg p k) (hpg p k) (hqg p k) T ω)
--           + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
--               coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedLimit`](https://prove2.me/theorems/8c696e51-9810-4fbb-b0f0-ded116e9b79e).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Selected supporting theorems: [`IsVectorItoVersion.itoFormula`](https://prove2.me/theorems/9fc109b4-701c-4220-bf8e-2dcb0c672023), [`ae_ae_tendsto_version_clamp`](https://prove2.me/theorems/4b4b00a1-8893-4a14-9b71-7455375e4cb1), [`ae_tendsto_drift_clamp`](https://prove2.me/theorems/0d88cd49-1116-49bb-b468-6962f08cda7d), [`ae_tendsto_quadVar_clamp`](https://prove2.me/theorems/16916452-8c4c-472a-be6e-b3b0e160f768), [`ae_tendsto_version_clamp_at`](https://prove2.me/theorems/749d431d-d8f1-44b6-ba64-5d3e7974a377).
--
--   Previous: [`exists_seq_ae_tendsto_stochInt_clamp`](https://prove2.me/theorems/bdc5e606-3379-4cae-bf91-d24473c129d6).
--
--   [Source excerpt, lines 172–183](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean#L172-L183) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean#L144-L320 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedLimit`, declaration `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded_coeff`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ')

theorem LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded_coeff_readable
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    (hf'c : Continuous f') (hf''c : Continuous f'')
    (hf''unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖f'' z - f'' w‖ ≤ ε)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by sorry
