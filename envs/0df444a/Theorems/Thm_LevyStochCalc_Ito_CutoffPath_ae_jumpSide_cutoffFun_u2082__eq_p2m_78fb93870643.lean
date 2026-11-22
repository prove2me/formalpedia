-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_CutoffPath_ae_jumpSide_cutoffFun_u2082__eq_p2m_78fb93870643
-- name    : LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun_u2082__eq_p2m_78fb93870643
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T10:09:41.751546+00:00
-- url     : https://prove2.me/theorems/52f9fb6f-9926-41f3-8b20-9089edb9e0b0
-- title:
--   ae jumpSide cutoffFun₂ eq
-- statement:
--   The source theorem `LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun₂_eq` is extracted from `LevyStochCalc.Ito.CutoffJumpTransfer`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffJumpTransfer_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump side of the Itô–Lévy formula under the state cut-off

Along a path confined to a ball the state cut-off moves the jump increment and the
compensator-drift integrand by the same quantity, and that quantity vanishes at every atom of the
random measure. An integrand vanishing at the atoms has compensated integral minus its
compensator, so the two moves cancel: the *sum* of the compensated integral of the jump increment
and the compensator-drift integral is the same for a state function and for its cut-off, even
though neither term is.

## Main definitions

* `jumpIncrLeft` — the jump increment of a state function along a path, read at the left limits.

## Main statements

* `measurable_jumpIncrLeft`, `markedProgressivelyMeasurable_jumpIncrLeft`,
  `markedPredictable_zeroExtPos_jumpIncrLeft` — its admissibility and the predictability of its
  zero extension.
* `ae_jumpSide_cutoffFun₂_eq` — the jump side is unchanged by the cut-off on the event that the
  path stays in the ball.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Ito.JumpFormula LevyStochCalc.Ito.JumpFormulaCutoff
open LevyStochCalc.Ito.JumpSplitting LevyStochCalc.Ito.JumpSide
open LevyStochCalc.Probability

universe u v

section Integrand

variable {Ω : Type u} {E : Type v} {n d : ℕ}

end Integrand

section Regularity

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {n d : ℕ}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}
  {w : ℝ → (Fin n → ℝ) → ℝ}

variable {ν : Measure E} [SigmaFinite ν]

end Regularity

section Transfer

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun_u2082__eq_p2m_78fb93870643
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : IsPoissonFiltration N ℱ)
    {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : 0 < m) (hTm : T < 3 * (m : ℝ))
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L))
    (hmv : Measurable fun p : Ω × ℝ × E =>
      jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp p.1 p.2.1 p.2.2)
    (hpv : MarkedProgressivelyMeasurable ℱ
      (jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp))
    (hqv : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤)
    (hmu : Measurable fun p : Ω × ℝ × E => jumpIncrLeft u coeffs Xp p.1 p.2.1 p.2.2)
    (hpu : MarkedProgressivelyMeasurable ℱ (jumpIncrLeft u coeffs Xp))
    (hqu : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖jumpIncrLeft u coeffs Xp ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hCdv : ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      IntegrableOn (fun q : ℝ × E => compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ)))
          coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν))
    (hCdu : ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      IntegrableOn (fun q : ℝ × E => compensatorDriftIntegrand u
          coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν))
    (hjump : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ k, θ k ∈ Set.Ioc (0 : ℝ) T ∧ ε k ∈ spanningSets ν j) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, g p ∂(N.N ω)
        = ∑ k : Fin K, g (θ k, ε k)) ∧
      ∀ k : Fin K,
        Xp (θ k) ω
          = leftLimPathAt Xp (θ k) ω + coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k)) :
    ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      Compensated.stochasticIntegral N ℱ hℱN
            (jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp) hmv hpv hqv T ω
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
              compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ q.1
                (leftLimPathAt Xp q.1 ω) q.2 ∂(referenceIntensity ν)
        = Compensated.stochasticIntegral N ℱ hℱN (jumpIncrLeft u coeffs Xp) hmu hpu hqu T ω
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
              compensatorDriftIntegrand u coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2
                ∂(referenceIntensity ν) := by sorry
