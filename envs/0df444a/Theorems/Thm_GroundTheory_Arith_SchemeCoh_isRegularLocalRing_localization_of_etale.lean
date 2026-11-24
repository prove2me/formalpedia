-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_localization_of_etale
-- name    : GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_etale
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:43.590077+00:00
-- url     : https://prove2.me/theorems/41f5a425-c4ab-4133-90f2-146755259a92
-- title:
--   Scheme Coh: is Regular Local Ring localization of etale
-- statement:
--   The Scheme Coh construction uses the is Regular Local Ring localization of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L35-L50

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
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
open IsLocalRing
universe u

theorem GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_etale {P B : Type*} [CommRing P] [CommRing B]
    [Algebra P B] [Algebra.Etale P B] [IsRegularRing P] (Q : Ideal B) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by sorry
