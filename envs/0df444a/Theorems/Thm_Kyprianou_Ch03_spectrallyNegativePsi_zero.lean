-- Prove2me | Theorems.Thm_Kyprianou_Ch03_spectrallyNegativePsi_zero
-- name    : Kyprianou.Ch03.spectrallyNegativePsi_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:15:18.885207+00:00
-- url     : https://prove2.me/theorems/cda73830-2eca-481b-861c-14357076b835
-- title:
--   Laplace exponent at zero for arbitrary spectrally negative Levy process
-- statement:
--   The Laplace exponent of a spectrally negative Levy process is zero at argument zero, for arbitrary process and Levy triplet.
-- source:
--   Kyprianou (2006) Chapter 3, Levy-Laplace exponent normalisation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem spectrallyNegativePsi_zero
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    L.ψ 0 = 0 := by
  sorry
end Kyprianou.Ch03
