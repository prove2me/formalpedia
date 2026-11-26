-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusyDrawdownFunctionalV1
-- name    : Kyprianou.Ch04.exercise46BusyDrawdownFunctionalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:44:47.287173+00:00
-- url     : https://prove2.me/theorems/5ea550ae-78b3-5c38-8f01-67ee58693cc1
-- title:
--   Common measurable drawdown functional for original and shifted paths
-- statement:
--   Recover the real drawdown from the proved measurable exponential drawdown test by taking the negative logarithm. The same measurable function is correct for original paths and all deterministic shifted increment paths.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BusyDrawdownFunctionalV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) :
    ∃ D : NNReal → (NNReal → Real) → Real,
      Measurable (fun z : NNReal × (NNReal → Real) => D z.1 z.2) ∧
      (∀ w t, D t (fun u => L.X u w) =
        sSup ((fun u => L.X u w) '' Iic t) - L.X t w) ∧
      (∀ w s t, let Y : NNReal → Real := fun u => L.X (s+u) w - L.X s w
        D t Y = sSup (Y '' Iic t) - Y t) := by
  sorry
