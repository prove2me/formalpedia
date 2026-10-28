-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardSelfMapRaw_isFixedPoint_readable
-- name    : LevyStochCalc.Ito.Picard.picardSelfMapRaw_isFixedPoint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:52.612329+00:00
-- url     : https://prove2.me/theorems/8d60ac0b-9ec8-46b3-ab34-28751499333d
-- title:
--   Picard Self-Map Satisfies Its Own Picard Equation
-- statement:
--   This is the fixed-point equation for the process produced from the Picard limit. Let $(\Omega,P)$ be a probability space, let $E$ have a sigma-finite measure $\nu$, let $W$ and $N$ be adapted Brownian and Poisson noises for a right-continuous filtration $\mathcal F'$, and assume the filtration, null-set, coefficient regularity, and coefficient Lipschitz hypotheses required by the type. Let $x_0\in\mathbb R^n$, $T>0$, $\beta>0$, and let $X_0$ be an admissible bounded process. Assume
--
--   $$\left(\operatorname{ENNReal.ofReal}\!\left(\frac{3\bigl(nL^2T+n dL^2+nL^2\bigr)}{2\beta}\right)\right)^{1/2}<1.$$
--
--   For every $t\in[0,T]$, the path of the raw self-map agrees almost surely and coordinatewise with the frozen Picard step taken along that same self-map:
--
--   $$\forall^{\mathrm{a.e.}}\,\omega\sim P,\ \forall i\in\operatorname{Fin}(n),\quad X(\operatorname{picardSelfMapRaw},t,\omega,i)=\operatorname{picardStepOnRawStop}(\operatorname{picardSelfMapRaw},t,\omega,i).$$
--
--   The statement identifies the constructed process with a solution of its own Picard equation on the finite window. It is the fixed-point ingredient used by the window-solution theorem.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--                   (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
--                   (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
--                     hLip x₀ hT X₀)
--                   (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
--                     x₀ hβ hT X₀ hq)).adapted i')
--               (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
--                 (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
--                 (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
--                   x₀ hT X₀)
--                 (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
--                   hβ hT X₀ hq)).sup_L2
--               hT.le x₀ t ω i
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardContractionFixedPoint`](https://prove2.me/theorems/b914ab33-ae92-46bd-8cc4-7cc082e284b0).
--
--   Definition modules: [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Ito/PicardOutputModification`](https://prove2.me/theorems/f2aa199f-3961-4748-8e22-7d7db164e159), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/PicardIntegrandFrozen`](https://prove2.me/theorems/a8112e63-ece0-4e4f-915e-522b9de90238).
--
--   Supporting theorems: [`picardSelfMapRaw_ae_eq`](https://prove2.me/theorems/9b049339-6c9f-4000-b846-f53555774ea7), [`picardSelfMapRaw_picardLimit_ae_eq`](https://prove2.me/theorems/f4ca4fcf-9668-4089-9376-14ea28fdaad0), [`picardStepOnRawStop_congr_ae`](https://prove2.me/theorems/e25c11bd-0c57-4831-ab92-f4ec98009984).
--
--   Previous: [`picardStepOnRawStop_congr_ae`](https://prove2.me/theorems/e25c11bd-0c57-4831-ab92-f4ec98009984).
--
--   [Source excerpt, lines 436–447](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardContractionFixedPoint.lean#L436-L447) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardContractionFixedPoint.lean#L411-L467 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardContractionFixedPoint`, declaration `LevyStochCalc.Ito.Picard.picardSelfMapRaw_isFixedPoint`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionFixedPoint

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardContractionFixedPoint.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)

theorem LevyStochCalc.Ito.Picard.picardSelfMapRaw_isFixedPoint_readable {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
          (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
          (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
            x₀ hT X₀)
          (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
            hβ hT X₀ hq)).X t ω i
        = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip
            (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
              (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                x₀ hT X₀)
              (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
                hβ hT X₀ hq)).measurable_path
            (fun i' =>
              (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
                (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
                (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
                  hLip x₀ hT X₀)
                (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                  x₀ hβ hT X₀ hq)).adapted i')
            (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
              (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                x₀ hT X₀)
              (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
                hβ hT X₀ hq)).sup_L2
            hT.le x₀ t ω i := by sorry
