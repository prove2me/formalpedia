-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvExponentSlopeLimit
-- name    : Kyprianou.Ch04.bvExponentSlopeLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T23:35:05.91388+00:00
-- url     : https://prove2.me/theorems/5e0c3a2b-833c-56e0-9f4a-a0305ace874b
-- title:
--   Bounded variation Laplace exponent has physical drift slope
-- statement:
--   Rewrite the exponent quotient as the physical drift minus the already-Proved normalised exponent deficit, then use its vanishing limit.
-- source:
--   Kyprianou (2006), Chapter 4, Corollaries 4.9 and 4.12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvExponentSlopeLimit
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) :
    Tendsto (fun beta : ℝ => L.ψ beta / beta)
      atTop (nhds L.drift) := by
  sorry
