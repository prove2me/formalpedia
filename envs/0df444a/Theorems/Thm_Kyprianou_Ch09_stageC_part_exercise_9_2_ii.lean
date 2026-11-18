-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_2_ii
-- name    : Kyprianou.Ch09.stageC_part_exercise_9_2_ii
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:50:12.867211+00:00
-- url     : https://prove2.me/theorems/d056630d-4926-4ca6-9af5-52ce9444ed3b
-- title:
--   Exercise 9.2.ii: Low-penalty scale root and convexity
-- statement:
--   Exercise 9.2.ii (Low-penalty scale root and convexity). Assumptions: X spectrally negative bounded variation with ψ(θ)=dθ−∫_(0,∞)(1−e^(−θy))Π(dy), δ>0, x≥0, d>q>ψ(1)>0; game supremum and infimum are interchangeable. Quantification: Every admissible δ,x; x* as Theorem 9.11 and all three whole subparts. Required mathematical conclusion in this subpart: When 1+delta < Z^(q)(x*), prove unique z* via Z^(q)(z*)=1+delta, z*<x*, convexity and boundary derivative facts.. The original chapter exercise specifies the formulas and companion cases: (i) If 1+δ≥Z^(q)(x*), game (9.48) has the value of Theorem 9.11. (ii) For 1+δ<Z^(q)(x*) prove unique z*<x* with Z^(q)(z*)=1+δ and convexity/endpoint derivatives for x↦e^xZ^(q)(z*−x). (iii) Game value e^x Z^(q)(z*−x), σ*=inf{t>0:Y_t^x=0}, τ*=inf{t>0:Y_t^x>z*}, continuous but nonsmooth at z*.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem exercise:9.2.ii; original PDF pp. [277, 278]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceReflected
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_part_exercise_9_2_ii :
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
    1 + δ < B1.scaleZ q W (B1.russianThreshold q W) →
    (∃! z : ℝ, 0 < z ∧ z < B1.russianThreshold q W ∧
      B1.scaleZ q W z = 1 + δ) ∧
    (∀ z : ℝ, 0 < z → z < B1.russianThreshold q W →
      B1.scaleZ q W z = 1 + δ →
      let v := fun x : ℝ => Real.exp x * B1.scaleZ q W (z - x)
      ConvexOn ℝ (Set.Ici 0) v ∧ ContinuousAt v z ∧
        DifferentiableWithinAt ℝ v (Set.Ici 0) 0 ∧
        0 < derivWithin v (Set.Ici 0) 0 ∧
        DifferentiableWithinAt ℝ v (Set.Iic z) z ∧
        derivWithin v (Set.Iic z) z = Real.exp z * (1 - q / d)) := by
  sorry

end Kyprianou.Ch09
