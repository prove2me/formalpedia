-- Prove2me | Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedDrawdownInfimumLaw
-- name    : Kyprianou.Ch04.fixedHorizonSignedDrawdownInfimumLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T12:32:08.113134+00:00
-- url     : https://prove2.me/theorems/8725e4d0-8223-4a5b-bd20-cadd42e84579
-- title:
--   Fixed-horizon signed drawdown and running infimum have identical distributions
-- statement:
--   Time reversal at each positive deterministic horizon identifies the law of terminal value minus the running supremum with the law of the running infimum.
-- source:
--   Kyprianou (2006), Corollary 4.9, fixed-horizon duality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.fixedHorizonSignedDrawdownInfimumLaw
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (ht : 0 < t) :
    let A : Ω → ℝ := fun w => L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t)
    let B : Ω → ℝ := fun w => sInf ((fun s : NNReal => L.X s w) '' Iic t)
    IdentDistrib A B P P := by
  sorry
