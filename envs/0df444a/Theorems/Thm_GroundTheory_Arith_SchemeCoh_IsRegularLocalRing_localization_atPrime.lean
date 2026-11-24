-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_localization_atPrime
-- name    : GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:55.167623+00:00
-- url     : https://prove2.me/theorems/d40d0ee9-ac01-4ddf-8aa3-d31b862c4d19
-- title:
--   Is Regular Local Ring: localization at Prime
-- statement:
--   The Is Regular Local Ring construction uses the localization at Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L345-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L345-L368

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

theorem GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by sorry
