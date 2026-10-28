-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_rawStop_congr_ae_readable
-- name    : LevyStochCalc.Ito.Picard.picardStep_rawStop_congr_ae_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:23.331985+00:00
-- url     : https://prove2.me/theorems/5db0caec-c4f8-4145-9624-8dfa7e854eeb
-- title:
--   Frozen And Unfrozen Picard Steps Agree Before The Horizon
-- statement:
--   This is a window-locality statement. Let $W,N,\mathcal F$ and the regular Lipschitz coefficients satisfy the stated Brownian, Poisson, measurability, and integrability hypotheses. Let $Z$ be a jointly measurable, progressively measurable state process with finite Bielecki norm and finite $S^2$-type supremum integral on every positive interval. If $0\leq T$, $0\leq t$, and $t\leq T$, then
--
--   $$\operatorname{picardStepOnRawStop}(Z,t,\omega)=\operatorname{picardStep}(Z,t,\omega)$$
--
--   for $P$-almost every $\omega$. Thus freezing the input path at $T$ does not alter the Picard step at earlier times. The lemma is used to pass from raw fixed-point equations on a window to the usual `picardStep` equation.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem picardStep_rawStop_congr_ae
--       (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
--       {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       (x₀ : Fin n → ℝ) {T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
--       (hZm : Measurable (Function.uncurry Z))
--       (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
--       (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
--       (hZS : ∀ T' : ℝ, 0 < T' →
--         ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
--       (hT : 0 ≤ T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
--       ∀ᵐ ω ∂P,
--         picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT x₀ t ω
--           = picardStep W N ℱ hℱW hℱN coeffs Z x₀
--               (measurable_sigma_comp_state coeffs hReg hZm)
--               (progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
--               (lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
--               (measurable_gamma_comp_state coeffs hReg hZm)
--               (markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
--               (lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
--               t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f).
--
--   Definition modules: [`LevyStochCalc/Ito/PicardIntegrandBounds`](https://prove2.me/theorems/e8adc16a-c6e7-47af-8474-43caed816e90), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02), [`LevyStochCalc/Ito/PicardStepMap`](https://prove2.me/theorems/21926b6e-8177-414a-981c-1a2486aea5bd), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Ito/PicardIntegrandFrozen`](https://prove2.me/theorems/a8112e63-ece0-4e4f-915e-522b9de90238).
--
--   Supporting theorems: [`picardStep_diffusion_congr_ae`](https://prove2.me/theorems/6c336559-f093-4ef9-8ae4-892731263519), [`picardStep_jump_congr_ae`](https://prove2.me/theorems/dbbc5d31-c9ed-480b-b61a-98ddb19cdde2).
--
--   Previous: [`ae_eq_of_solvesOn`](https://prove2.me/theorems/68acae9c-cef9-4b55-9b63-0571ce263cb6) · Next: [`solvesOn_of_isFixedPoint`](https://prove2.me/theorems/65f806f4-e0d8-4e52-9f10-b2384eb2ab37).
--
--   [Source excerpt, lines 338–357](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardWindow.lean#L338-L357) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardWindow.lean#L337-L404 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardWindow`, declaration `LevyStochCalc.Ito.Picard.picardStep_rawStop_congr_ae`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

theorem LevyStochCalc.Ito.Picard.picardStep_rawStop_congr_ae_readable
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
    (hZS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hT : 0 ≤ T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P,
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT x₀ t ω
        = picardStep W N ℱ hℱW hℱN coeffs Z x₀
            (measurable_sigma_comp_state coeffs hReg hZm)
            (progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
            (lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
            (measurable_gamma_comp_state coeffs hReg hZm)
            (markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
            (lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
            t ω := by sorry
