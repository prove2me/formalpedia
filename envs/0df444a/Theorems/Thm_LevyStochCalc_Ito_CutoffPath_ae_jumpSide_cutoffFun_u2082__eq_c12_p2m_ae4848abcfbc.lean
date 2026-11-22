-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_CutoffPath_ae_jumpSide_cutoffFun_u2082__eq_c12_p2m_ae4848abcfbc
-- name    : LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun_u2082__eq_c12_p2m_ae4848abcfbc
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:38:30.302355+00:00
-- url     : https://prove2.me/theorems/7cada499-3630-4de4-a118-d708607dbdea
-- title:
--   ae jumpSide cutoffFun₂ eq c12
-- statement:
--   The source theorem `LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun₂_eq_c12` is extracted from `LevyStochCalc.Ito.CutoffC12`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffGlobalBounds_F000
import Definitions.Def_LevyStochCalc_Ito_CutoffJumpTransfer_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuityC12_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The time–space cut-off of a `C^{1,2}` state function

The time–space cut-off of radius `R` multiplies a state function by a jointly `C²` factor, so the
cut-off of a `C^{1,2}` function is again of class `C^{1,2}`. Its time derivative, gradient and
Hessian vanish outside the closed ball of radius `2R` and are continuous, hence are bounded
everywhere by one constant. Along a path confined to a ball the cut-off leaves the jump side of
the Itô–Lévy formula — the compensated integral of the jump increment plus the compensator-drift
integral — unchanged, and that transfer needs of the state function only the joint continuity of
the function and of its cut-off.

## Main statements

* `LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun₂_c12` — one constant bounds
  the time derivative, every gradient entry and every Hessian entry of the cut-off of a `C^{1,2}`
  function, at every time and every state.
* `LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun₂_eq_c12` — for a `C^{1,2}` state function
  the jump side is unchanged by the cut-off on the event that the path stays in the ball.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormulaCutoff

open LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

end LevyStochCalc.Ito.JumpFormulaCutoff

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Ito.JumpFormula LevyStochCalc.Ito.JumpFormulaCutoff
open LevyStochCalc.Ito.JumpSplitting LevyStochCalc.Ito.JumpSide
open LevyStochCalc.Probability

universe u v

section Transfer

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun_u2082__eq_c12_p2m_ae4848abcfbc
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : IsPoissonFiltration N ℱ)
    {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : IsC12 u)
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
