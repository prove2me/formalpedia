-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_exists_picard_integrands_of_rightCont
-- name    : LevyStochCalc.BSDEJ.Solves.exists_picard_integrands_of_rightCont
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:03:12.318968+00:00
-- url     : https://prove2.me/theorems/540b1d90-4933-40fe-b3ba-28ccb3f68484
-- title:
--   exists picard integrands of rightCont
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.exists_picard_integrands_of_rightCont` is extracted from `LevyStochCalc.BSDEJ.PicardTerminal`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardTerminal_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The terminal datum of a Picard step and its martingale representation

A Picard step of a backward equation with jumps is driven by the variable `ξ + ∫_0^T b_s ds`,
where `ξ` is the terminal value and `b` the generator frozen along the previous iterate:
`terminalDatum` is that variable. It is square integrable and measurable before the horizon as
soon as `ξ` is and `b` is progressive of finite energy; progressivity for the right-continuous
filtration already suffices when `b` vanishes off the horizon. `centred` subtracts the mean, and the
predictable representation property of a Lévy driver writes the centred terminal datum as the
sum of a multidimensional Itô integral and a compensated integral over the horizon, whose
integrands carry the measurability, progressivity, vanishing and energy fields the backward
equation is written with.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### The terminal datum of a Picard step -/

/-! ### Centring -/

/-! ### The martingale representation of the centred terminal datum -/

section Representation

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

theorem _root_.LevyStochCalc.BSDEJ.Solves.exists_picard_integrands_of_rightCont (D : Driver.LevyDriver.{u, v, w} P d ν) {T : ℝ}
    (hT : 0 < T) {ξ : Ω → ℝ} (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)
    {b : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable (augJoint D).rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∃ (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
      (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
      (hZp : ∀ i : Fin d, Probability.ProgressivelyMeasurable (augJoint D)
        fun ω s => Z s ω i)
      (hZv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
      (hZq : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
      (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
      (hUp : Probability.MarkedProgressivelyMeasurable (augJoint D) fun ω s e => U s ω e)
      (hUv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
      (hUq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤),
      centred P (terminalDatum ξ b T) =ᵐ[P] fun ω =>
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
            D.isBrownianFiltration_aug Z hZm hZp (sq_int_global_of_vanishing hZv hZq) T ω
          + Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
            (fun ω' s e => U s ω' e) hUm hUp (marked_sq_int_global_of_vanishing hUv hUq) T ω := by sorry
