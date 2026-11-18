-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_2_iii
-- name    : Kyprianou.Ch09.stageC_part_exercise_9_2_iii
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:50:41.146609+00:00
-- url     : https://prove2.me/theorems/a2f6b46e-d192-402a-9f3e-6087b8aa8a50
-- title:
--   Exercise 9.2.iii: Game saddle stopping times and fit
-- statement:
--   Exercise 9.2.iii (Game saddle stopping times and fit). Assumptions: X spectrally negative bounded variation with ψ(θ)=dθ−∫_(0,∞)(1−e^(−θy))Π(dy), δ>0, x≥0, d>q>ψ(1)>0; game supremum and infimum are interchangeable. Quantification: Every admissible δ,x; x* as Theorem 9.11 and all three whole subparts. Required mathematical conclusion in this subpart: Derive game value e^x Z^(q)(z*-x), saddle times, continuous fit and failure of smooth fit.. The original chapter exercise specifies the formulas and companion cases: (i) If 1+δ≥Z^(q)(x*), game (9.48) has the value of Theorem 9.11. (ii) For 1+δ<Z^(q)(x*) prove unique z*<x* with Z^(q)(z*)=1+δ and convexity/endpoint derivatives for x↦e^xZ^(q)(z*−x). (iii) Game value e^x Z^(q)(z*−x), σ*=inf{t>0:Y_t^x=0}, τ*=inf{t>0:Y_t^x>z*}, continuous but nonsmooth at z*.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem exercise:9.2.iii; original PDF pp. [277, 278]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceReflected
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_part_exercise_9_2_iii :
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (q δ : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hψ : 0 < ψ 1) (hq : ψ 1 < q) (hqd : q < d)
    (hδ : 0 < δ) (hScale : B1.IsScale ψ q W),
    ∀ z : ℝ, 0 < z → z < B1.russianThreshold q W →
      B1.scaleZ q W z = 1 + δ →
      ∀ x : ℝ, 0 ≤ x →
        B1.russianGameValue P F X q x δ =
          Real.exp x * B1.scaleZ q W (z - x) ∧
        B1.RussianGameSaddle P F X q x δ
          (fun ω => B1.firstStrictReflectedAbove X x z ω)
          (fun ω => sInf {t : WithTop ℝ≥0 |
            ∃ s : ℝ≥0,
              0 < s ∧ max x
                (B1.pathSupAt X s ω) - X s ω = 0 ∧
                t = (s : WithTop ℝ≥0)}) ∧
        ContinuousAt
          (fun y : ℝ => Real.exp y * B1.scaleZ q W (z - y)) z ∧
        ¬ B1.SmoothFitAt
          (fun y : ℝ => Real.exp y * B1.scaleZ q W (z - y)) z := by
  sorry

end Kyprianou.Ch09
