-- Prove2me | Theorems.Thm_Kyprianou_Ch04_infimumClockWhLimit
-- name    : Kyprianou.Ch04.infimumClockWhLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:49:11.161543+00:00
-- url     : https://prove2.me/theorems/599c48be-86c6-5d9e-b647-5bfc6d8a3e9c
-- title:
--   infimumClockWhLimit
-- statement:
--   The product-clock identity holds eventually because a fixed nonzero exponent cannot equal all sufficiently small discounts. Transfer the scalar limit through this eventual equality.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.infimumClockWhLimit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator : ¬ (∀ᵐ w : Ω ∂P, Antitone (fun t : NNReal => L.X t w)))
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hq0 : Tendsto q atTop (nhds 0))
    (beta : ℝ) (hb : 0 < beta) (hpsi : L.ψ beta ≠ 0) :
    Tendsto (fun n : ℕ => ∫ z : Ω × ℝ, Real.exp (beta * sInf ((fun s : NNReal => L.X s z.1) '' Iic z.2.toNNReal))
      ∂(P.prod (expMeasure (q n)))) atTop (nhds (max 0 (sInf ((fun theta : ℝ => L.ψ theta / theta) '' Ioi 0)) * beta / L.ψ beta)) := by
  sorry
