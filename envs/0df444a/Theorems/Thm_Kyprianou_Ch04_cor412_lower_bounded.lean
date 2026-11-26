-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_lower_bounded
-- name    : Kyprianou.Ch04.cor412_lower_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:35:16.136418+00:00
-- url     : https://prove2.me/theorems/cfbec52a-bd33-5270-befe-ee85fe046a1a
-- title:
--   Positive mean excludes antitone paths and ensures almost sure lower boundedness
-- statement:
--   Positive mean excludes antitone paths and ensures almost sure lower boundedness.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_positive_exponent
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_positiveMeanClassification
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_lower_bounded
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici 0) 0) :
    (¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w))) ∧
      (∀ᵐ w ∂P, BddBelow (range (fun t : NNReal => L.X t w))) := by sorry
