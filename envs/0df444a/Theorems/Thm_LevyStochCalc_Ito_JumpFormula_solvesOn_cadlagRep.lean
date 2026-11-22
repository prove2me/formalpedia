-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_solvesOn_cadlagRep
-- name    : LevyStochCalc.Ito.JumpFormula.solvesOn_cadlagRep
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:57:23.502932+00:00
-- url     : https://prove2.me/theorems/b66fe14f-4948-4bbd-9377-cf09d6bcda7e
-- title:
--   solvesOn cadlagRep
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.solvesOn_cadlagRep` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg representative of a solution path

The Itô–Lévy formula at bounded derivatives asks for left limits of the solution at every sample
point and every time, while the well-posedness theorem produces paths that are càdlàg only on a
measurable set `G` of full measure. `cadlagRep G X` is the path map that agrees with `X` on `G` at
nonnegative times, is the constant zero path off `G`, and is frozen at the zero state before time
zero. It is càdlàg at every sample point and every time, adapted whenever `G` belongs to the
initial σ-algebra, progressively measurable because it is right-continuous everywhere, and solves
the equation on every window, because both stochastic integrals depend only on the class of their
integrand.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section CadlagRep

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

variable {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}

variable (hGp : ∀ ω ∈ G, ∀ t : ℝ, 0 ≤ t →
  Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
    ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))

end CadlagRep

section Representative

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E) {x₀ : Fin n → ℝ}
  {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormula.solvesOn_cadlagRep (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hσq : ∀ (i : Fin n) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hXm : Measurable (Function.uncurry X))
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = x₀)
    (hGp : ∀ ω ∈ G, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (hXsol : ∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) (T : ℝ) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ (cadlagRep G X) T := by sorry
