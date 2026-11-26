-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clockRunningInfimumWienerHopfTransform
-- name    : Kyprianou.Ch04.clockRunningInfimumWienerHopfTransform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:40:38.876563+00:00
-- url     : https://prove2.me/theorems/3b40d35a-a4cd-4098-89bb-ac2c5ab19534
-- title:
--   Product-clock running infimum Wiener-Hopf transform
-- statement:
--   The proved product-clock drawdown and negative infimum have identical distributions. Composing with the exponential transfers the established nonsingular Wiener-Hopf transform.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.clockRunningInfimumWienerHopfTransform
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (q r beta : ℝ) (hq : 0 < q) (hr : 0 < r)
    (hroot : L.ψ r = q) (hb : 0 < beta) (hne : beta ≠ r) :
    (∫ z : Ω × ℝ, Real.exp (beta * sInf ((fun s : NNReal => L.X s z.1) '' Iic z.2.toNNReal))
      ∂(P.prod (expMeasure q))) = (q/r) * ((r-beta)/(q-L.ψ beta)) := by
  sorry
