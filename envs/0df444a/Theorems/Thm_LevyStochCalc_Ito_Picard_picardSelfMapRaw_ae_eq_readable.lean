-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardSelfMapRaw_ae_eq_readable
-- name    : LevyStochCalc.Ito.Picard.picardSelfMapRaw_ae_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:44.240061+00:00
-- url     : https://prove2.me/theorems/9b049339-6c9f-4000-b846-f53555774ea7
-- title:
--   Raw Self-Map Modification Equals the Picard Step
-- statement:
--   This states that the path component of the raw Picard self-map is an almost-everywhere modification of the corresponding stopped Picard step.
--
--   Let $P$ be a probability measure, $W$ and $N$ be the Brownian and Poisson drivers, and let $\mathcal F$ be right-continuous, satisfy the filtration-at-zero and null-set hypotheses, and be compatible with both drivers. Let the coefficients be regular and Lipschitz. Let $Z$ be jointly measurable and progressively measurable coordinatewise, with
--   $\operatorname{bieleckiNorm}(0,T,Z)<\top$ for $T>0$.
--
--   For every $t\in\mathbb R$,
--
--   $$\bigl(\operatorname{picardSelfMapRaw}(Z)\bigr).X_t
--   =\operatorname{picardStepOnRawStop}(Z,t)\quad\text{a.e. }[P].$$
--
--   This identifies the modification used by the self-map with the explicitly defined Picard step at each fixed time.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem picardSelfMapRaw_ae_eq
--       (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
--       (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
--       (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
--       (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
--       (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
--       (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
--       {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
--       {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
--       (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
--       (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) (t : ℝ) :
--       (picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X t
--         =ᵐ[P] picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardOutputModification`](https://prove2.me/theorems/f2aa199f-3961-4748-8e22-7d7db164e159).
--
--   Definition modules: [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02), [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Ito/PicardIntegrandFrozen`](https://prove2.me/theorems/a8112e63-ece0-4e4f-915e-522b9de90238).
--
--   [Source excerpt, lines 482–498](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardOutputModification.lean#L482-L498) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardOutputModification.lean#L481-L530 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardOutputModification`, declaration `LevyStochCalc.Ito.Picard.picardSelfMapRaw_ae_eq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardOutputModification

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardOutputModification.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

theorem LevyStochCalc.Ito.Picard.picardSelfMapRaw_ae_eq_readable
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) (t : ℝ) :
    (picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X t
      =ᵐ[P] picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t := by sorry
