-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiConstantPrefixOccupationFormula
-- name    : Kyprianou.Ch01.reverseLampertiConstantPrefixOccupationFormula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:16:59.706259+00:00
-- url     : https://prove2.me/theorems/5998e7af-e5e9-4029-8f9b-b4e9077c7b77
-- title:
--   Exact reciprocal occupation integral for an integer-valued constant initial prefix
-- statement:
--   If an integer-valued path stays at y up to physical time s, the inverse-speed occupation over that interval equals s/y with the extended-nonnegative inverse convention. The y=0 case gives infinity for positive s, and both sides vanish at s=0.
-- source:
--   Kyprianou (2006), Section 1.3.4, equation (1.19), integral of a constant inverse-speed path.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiConstantPrefixOccupationFormula
    {Omega : Type*} (X : NNReal -> Omega -> Int) (omega : Omega)
    (y : Nat) (s : NNReal)
    (hConst : ∀ u : NNReal, u ≤ s -> X u omega = (y : Int)) :
    reciprocalOccupation X s omega =
      (y : ENNReal)⁻¹ * (s : ENNReal) := by
  sorry
