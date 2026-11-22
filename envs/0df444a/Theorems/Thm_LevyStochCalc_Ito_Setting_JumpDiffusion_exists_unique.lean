-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Setting_JumpDiffusion_exists_unique
-- name    : LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:07:53.47476+00:00
-- url     : https://prove2.me/theorems/a4228144-c7f3-474f-ad0b-3d2460c34cfb
-- title:
--   Strong existence and uniqueness for a Brownian–Poisson jump diffusion
-- statement:
--   For a multidimensional Brownian motion and Poisson random measure compatible with a common right-continuous filtration, a completed initial σ-algebra, appropriate initial-value data and jump-diffusion coefficients satisfying the source Lipschitz and regularity predicates, there exists a solution on all horizons. Any other solution satisfying the same SolvesOn equations agrees with it almost surely at each nonnegative time. The conclusion is formulated in the source JumpDiffusion and Picard solution predicates.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc/blob/main/LevyStochCalc/Ito/PicardFixedPoint.lean

import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence and uniqueness via the Banach fixed-point theorem

This file packages Banach's fixed-point theorem (`ContractingWith.fixedPoint`)
in the `∃!` shape of a Picard iteration, and states the existence/uniqueness
theorem for the jump-diffusion SDE in the form consumed by `Ito/Setting.lean`,
forwarding to `exists_jumpDiffusion_unique_of_solvesOn` in
`Ito/PicardWellPosed.lean`.

## Contents

* `picardFixedPoint_generic`, `picardFixedPoint`, `picardFixedPoint_of_exists`
  — the abstract fixed-point packaging.
* `picardFixedPoint_jumpDiffusion_exists_unique` — the concrete
  existence/uniqueness statement for the jump-diffusion SDE, relative to a
  filtration satisfying the usual conditions.
* `JumpDiffusion.exists_unique`, `JumpDiffusion.agree_at_zero` — the form
  consumed by `Ito/Setting.lean`.
-/
open MeasureTheory ProbabilityTheory Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

end LevyStochCalc.Ito.Picard

/-! ## Literature theorem: `JumpDiffusion.exists_unique`

This is the headline existence-and-uniqueness theorem cited from
Applebaum 2009 Theorem 6.2.9 / Ikeda-Watanabe IV. Its qualified name is
`LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` — we re-open
that namespace explicitly here so the original location in
`Ito/Setting.lean` (a module that this file imports) is preserved at
the level of qualified names.

**Why the theorem lives here, not in `Ito/Setting.lean`**: the proof
forwards through `picardFixedPoint_jumpDiffusion_exists_unique` (above),
which forwards to `exists_jumpDiffusion_unique_of_solvesOn` in
`Ito/PicardWellPosed.lean`. Putting the theorem in `LevyStochCalc.Ito.Setting`
would require that module to import `LevyStochCalc.Ito.PicardWellPosed`,
which already imports `LevyStochCalc.Ito.Setting` for the `JumpDiffusion`
structure definition, creating a cycle. -/

namespace LevyStochCalc.Ito.Setting
namespace JumpDiffusion

theorem _root_.LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    {L : ℝ} (hL : JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs ν) :
    ∃ jd : JumpDiffusion W N coeffs x₀,
      (∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd.X T)
        ∧ ∀ jd' : JumpDiffusion W N coeffs x₀,
            (∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd'.X T) →
              ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω := by sorry
