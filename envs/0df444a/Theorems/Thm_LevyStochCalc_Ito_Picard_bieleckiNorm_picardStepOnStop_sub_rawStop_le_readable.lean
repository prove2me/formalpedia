-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_picardStepOnStop_sub_rawStop_le_readable
-- name    : LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnStop_sub_rawStop_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:46.715569+00:00
-- url     : https://prove2.me/theorems/f7bce8db-81a1-4513-838e-14d438224f96
-- title:
--   Bielecki Contraction Bound Against a Raw State Process
-- statement:
--   This gives a Bielecki-norm bound for the difference between a Picard step along a bounded process and a Picard step along a raw state process.
--
--   Let the Brownian and Poisson drivers, filtrations, coefficients, and regularity assumptions be as in the type. Let $Z$ be measurable and progressively measurable coordinatewise with
--   $\operatorname{bieleckiNorm}(0,T,Z)<\top$, let $x_0$ be the initial state, let $X$ be an $S$-bounded process on $[0,T]$, and assume $\beta>0$ and $T>0$. Then
--
--   $$\begin{aligned}
--   &\operatorname{bieleckiNorm}\bigl(\beta,T,\operatorname{picardStepOnStop}(X)-\operatorname{picardStepOnRawStop}(Z)\bigr)\\
--   &\quad\le \left(\operatorname{ofReal}\left(\frac{3(nL^2T+ndL^2+nL^2)}{2\beta}\right)\right)^{1/2}
--   \operatorname{bieleckiNorm}\bigl(\beta,T,X-Z\bigr).
--   \end{aligned}$$
--
--   The Bielecki norms are `ENNReal`-valued. This is the contraction estimate used to compare the self-map with a raw process.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bieleckiNorm_picardStepOnStop_sub_rawStop_le {L : ℝ}
--       (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
--       (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z s ω i)
--       (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
--       (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
--       (X : SBoundedProcess (n := n) P ℱ' T) :
--       bieleckiNorm (P := P) β T (fun t ω i =>
--           picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
--             - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t ω i)
--         ≤ (ENNReal.ofReal
--               ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
--                 / (2 * β))) ^ ((1 : ℝ) / 2)
--           * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardContractionEstimate`](https://prove2.me/theorems/8cad574e-6914-4d17-98ca-b6df8ebe8b41).
--
--   Definition modules: [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/PicardIntegrandFrozen`](https://prove2.me/theorems/a8112e63-ece0-4e4f-915e-522b9de90238), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Previous: [`exists_bieleckiWeight_rate_lt_one`](https://prove2.me/theorems/2424b633-168d-49a1-be31-197cd8b56a43).
--
--   [Source excerpt, lines 432–445](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardContractionEstimate.lean#L432-L445) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardContractionEstimate.lean#L430-L487 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardContractionEstimate`, declaration `LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnStop_sub_rawStop_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionEstimate

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardContractionEstimate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
omit [ℱ'.IsRightContinuous]

theorem LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnStop_sub_rawStop_le_readable {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i) := by sorry
