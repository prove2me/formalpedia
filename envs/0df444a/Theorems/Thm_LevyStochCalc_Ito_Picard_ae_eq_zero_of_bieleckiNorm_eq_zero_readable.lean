-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_ae_eq_zero_of_bieleckiNorm_eq_zero_readable
-- name    : LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:46.024136+00:00
-- url     : https://prove2.me/theorems/03028af0-5e72-4f50-a46d-8baf738dd95f
-- title:
--   Vanishing Bielecki Norm Implies Almost-Everywhere Vanishing
-- statement:
--   This states that a zero Bielecki norm forces a path map to vanish almost everywhere at each time in the window.
--
--   Let $P$ be a probability measure, $Z:\mathbb R\to\Omega\to\mathbb R^n$, and assume every coordinate $Z(u,\cdot,i)$ is measurable. If
--
--   $$\operatorname{bieleckiNorm}(\beta,T,Z)=0,$$
--
--   then for every $t\in[0,T]$,
--
--   $$\forall^{\mathrm{a.e.}}\,\omega\sim P,\ \forall i<n,\quad Z(t,\omega,i)=0.$$
--
--   The Bielecki norm and its integrals take values in $[0,\infty]$. This lemma converts a norm identity into coordinatewise almost-everywhere equality on a fixed window.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_eq_zero_of_bieleckiNorm_eq_zero {β T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
--       (hZs : ∀ (u : ℝ) (i : Fin n), Measurable fun ω => Z u ω i)
--       (h : bieleckiNorm (P := P) β T Z = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
--       ∀ᵐ ω ∂P, ∀ i, Z t ω i = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardContractionFixedPoint`](https://prove2.me/theorems/b914ab33-ae92-46bd-8cc4-7cc082e284b0).
--
--   Definition modules: [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02).
--
--   Previous: [`bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero`](https://prove2.me/theorems/f04f380e-8b10-422c-b9f4-8f255f38cc70) · Next: [`picardSelfMapRaw_picardLimit_ae_eq`](https://prove2.me/theorems/f4ca4fcf-9668-4089-9376-14ea28fdaad0).
--
--   [Source excerpt, lines 236–239](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardContractionFixedPoint.lean#L236-L239) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardContractionFixedPoint.lean#L233-L263 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardContractionFixedPoint`, declaration `LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg hLip

theorem LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero_readable {β T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZs : ∀ (u : ℝ) (i : Fin n), Measurable fun ω => Z u ω i)
    (h : bieleckiNorm (P := P) β T Z = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i, Z t ω i = 0 := by sorry
