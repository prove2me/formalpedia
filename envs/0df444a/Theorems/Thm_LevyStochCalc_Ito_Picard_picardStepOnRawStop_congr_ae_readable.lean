-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardStepOnRawStop_congr_ae_readable
-- name    : LevyStochCalc.Ito.Picard.picardStepOnRawStop_congr_ae_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:48.686276+00:00
-- url     : https://prove2.me/theorems/e25c11bd-0c57-4831-ab92-f4ec98009984
-- title:
--   Almost-Everywhere Congruence Of The Frozen Picard Step
-- statement:
--   This is an auxiliary locality statement for the frozen Picard step. In the setting of a probability space $(\Omega,P)$, a sigma-finite mark measure $\nu$, Brownian motion $W$, Poisson random measure $N$, filtration $\mathcal F'$, regular Lipschitz coefficients, initial state $x_0$, and two jointly measurable progressively measurable processes $Z_1,Z_2$ with finite Bielecki norms, assume
--
--   1. $Z_1$ and $Z_2$ agree $P$-almost surely at every coordinate for every time in $[0,T]$;
--   2. $\beta>0$ and $T>0$.
--
--   Then, for every $t\in[0,T]$, their frozen Picard steps agree almost surely, coordinatewise:
--
--   $$\forall^{\mathrm{a.e.}}\,\omega\sim P,\ \forall i\in\operatorname{Fin}(n),\quad \operatorname{picardStepOnRawStop}(Z_1,t,\omega,i)=\operatorname{picardStepOnRawStop}(Z_2,t,\omega,i).$$
--
--   This technical congruence lemma allows almost-sure equality of inputs to be propagated through the Picard operator.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem picardStepOnRawStop_congr_ae
--       {Z₁ : ℝ → Ω → (Fin n → ℝ)} (h₁m : Measurable (Function.uncurry Z₁))
--       (h₁a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₁ s ω i)
--       (h₁b : bieleckiNorm (P := P) 0 T Z₁ < ⊤)
--       {Z₂ : ℝ → Ω → (Fin n → ℝ)} (h₂m : Measurable (Function.uncurry Z₂))
--       (h₂a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₂ s ω i)
--       (h₂b : bieleckiNorm (P := P) 0 T Z₂ < ⊤)
--       (heq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i, Z₁ t ω i = Z₂ t ω i)
--       {β : ℝ} (hβ : 0 < β) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
--       ∀ᵐ ω ∂P, ∀ i,
--         picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ t ω i
--           = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ t ω i
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardContractionFixedPoint`](https://prove2.me/theorems/b914ab33-ae92-46bd-8cc4-7cc082e284b0).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Ito/PicardIntegrandFrozen`](https://prove2.me/theorems/a8112e63-ece0-4e4f-915e-522b9de90238).
--
--   Supporting theorems: [`ae_eq_zero_of_bieleckiNorm_eq_zero`](https://prove2.me/theorems/03028af0-5e72-4f50-a46d-8baf738dd95f), [`bieleckiNorm_picardStepOnRawStop_diff_le`](https://prove2.me/theorems/9a6322fc-eee3-47fb-b0eb-e8fa350bde78), [`measurable_picardStepOnRawStop_slice`](https://prove2.me/theorems/b756fd53-bc8d-4424-9fc0-745ef08f7652).
--
--   Previous: [`bieleckiNorm_picardStepOnRawStop_diff_le`](https://prove2.me/theorems/9a6322fc-eee3-47fb-b0eb-e8fa350bde78) · Next: [`picardSelfMapRaw_isFixedPoint`](https://prove2.me/theorems/8d60ac0b-9ec8-46b3-ab34-28751499333d).
--
--   [Source excerpt, lines 376–387](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardContractionFixedPoint.lean#L376-L387) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardContractionFixedPoint.lean#L374-L407 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardContractionFixedPoint`, declaration `LevyStochCalc.Ito.Picard.picardStepOnRawStop_congr_ae`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
omit [ℱ'.IsRightContinuous]

theorem LevyStochCalc.Ito.Picard.picardStepOnRawStop_congr_ae_readable
    {Z₁ : ℝ → Ω → (Fin n → ℝ)} (h₁m : Measurable (Function.uncurry Z₁))
    (h₁a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₁ s ω i)
    (h₁b : bieleckiNorm (P := P) 0 T Z₁ < ⊤)
    {Z₂ : ℝ → Ω → (Fin n → ℝ)} (h₂m : Measurable (Function.uncurry Z₂))
    (h₂a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₂ s ω i)
    (h₂b : bieleckiNorm (P := P) 0 T Z₂ < ⊤)
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i, Z₁ t ω i = Z₂ t ω i)
    {β : ℝ} (hβ : 0 < β) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ t ω i
        = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ t ω i := by sorry
