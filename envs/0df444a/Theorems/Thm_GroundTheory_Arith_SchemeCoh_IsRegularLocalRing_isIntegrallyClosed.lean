-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isIntegrallyClosed
-- name    : GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:17.489591+00:00
-- url     : https://prove2.me/theorems/97f3b621-19b9-4142-bc95-0ff5d2b52ac4
-- title:
--   Is Regular Local Ring: is Integrally Closed
-- statement:
--   The Is Regular Local Ring construction uses the is Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFD.lean#L267-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFD.lean#L267-L269

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFD
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
open IsLocalRing Ideal Module
universe u

theorem GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsIntegrallyClosed R := by sorry
