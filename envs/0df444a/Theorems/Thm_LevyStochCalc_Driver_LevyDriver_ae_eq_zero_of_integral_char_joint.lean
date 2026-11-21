-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_ae_eq_zero_of_integral_char_joint
-- name    : LevyStochCalc.Driver.LevyDriver.ae_eq_zero_of_integral_char_joint
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:22:12.273852+00:00
-- url     : https://prove2.me/theorems/a26134ae-f953-4637-96e8-e6d9d1aa8684
-- title:
--   ae eq zero of integral char joint
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.ae_eq_zero_of_integral_char_joint` is extracted from `LevyStochCalc.Driver.JointCharacters`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointCharacters_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Product characters of a Lévy driver separate

The coordinate values of the Brownian motion before `T` and the window counts of the Poisson
random measure before `T` form one family of real random variables, indexed by a sum type. Its
cylinder characters are the products of a Brownian cylinder character and a window character,
and the σ-algebra it generates is `σ(W_{≤T}) ⊔ windowSigma N T`, whose augmentation contains the
joint natural filtration at `T`. The generic separation theorem
`Probability.ae_eq_zero_of_integral_char_cylinder_eq_zero` therefore shows that an integrable
weight, measurable for the augmented joint filtration at `T` and orthogonal to every product
character, vanishes almost everywhere.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

theorem _root_.LevyStochCalc.Driver.LevyDriver.ae_eq_zero_of_integral_char_joint (T : ℝ) {Z : Ω → ℂ} (hZ : Integrable Z P)
    (hZm : AEStronglyMeasurable[Probability.aug (D.filtration T) ‹MeasurableSpace Ω› P] Z P)
    (h : ∀ (F : Finset (Fin d × Set.Iic T)) (G : Finset (Poisson.WindowSet E ν T))
      (w : F → ℝ) (v : G → ℝ),
      ∫ ω, Complex.exp (((∑ p : F, (D.W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((∑ B : G, (D.N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal
            * v B : ℝ) : ℂ) * Complex.I) * Z ω ∂P = 0) :
    Z =ᵐ[P] 0 := by sorry
