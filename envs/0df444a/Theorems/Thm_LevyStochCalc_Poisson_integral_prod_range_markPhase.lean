-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_integral_prod_range_markPhase
-- name    : LevyStochCalc.Poisson.integral_prod_range_markPhase
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T22:19:08.693055+00:00
-- url     : https://prove2.me/theorems/7ab01776-0f90-46af-b698-f912036278c4
-- title:
--   integral prod range markPhase
-- statement:
--   The source theorem `LevyStochCalc.Poisson.integral_prod_range_markPhase` is extracted from `LevyStochCalc.Poisson.PoissonSplitting`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson splitting

A Poisson number `K` of independent marks `X₀, X₁, …` with common law `ρ`, independent of `K`,
scattered over pairwise disjoint measurable sets `B₁, …, Bₙ`: the counts
`Nᵢ = ∑_{j < K} 1_{Bᵢ}(Xⱼ)` are independent, and `Nᵢ` is Poisson with mean `r ρ(Bᵢ)`.

The joint characteristic function is computed by conditioning on `K`: given `K = m`, the
marks are independent, so `𝔼 exp(i ∑ᵢ tᵢ Nᵢ) = ∑ₘ P(K = m) cₘ` with
`c = ∑ᵢ ρ(Bᵢ) e^{i tᵢ} + (1 − ∑ᵢ ρ(Bᵢ))`, and the exponential series gives
`exp(r (c − 1)) = ∏ᵢ exp(r ρ(Bᵢ) (e^{i tᵢ} − 1))`, the characteristic function of the product of
the Poisson laws.
-/

open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} [IsProbabilityMeasure ρ]
  {K : Ω → ℕ} {X : ℕ → Ω → 𝓧} {r : ℝ≥0}

section CharFun

variable {n : ℕ} (B : Fin n → Set 𝓧) (t : Fin n → ℝ)

variable {B t}

omit [IsProbabilityMeasure ρ] in

theorem _root_.LevyStochCalc.Poisson.integral_prod_range_markPhase (hB : ∀ i, MeasurableSet (B i)) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) :
    ∫ ω, ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω) ∂P
      = ∑' m, (P.real (K ⁻¹' {m}) : ℂ) * (∫ x, markPhase B t x ∂ρ) ^ m := by sorry
