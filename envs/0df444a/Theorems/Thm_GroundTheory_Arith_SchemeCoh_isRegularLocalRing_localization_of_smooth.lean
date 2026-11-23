-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_localization_of_smooth
-- name    : GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:44.02178+00:00
-- url     : https://prove2.me/theorems/0cad3a2c-3646-45b9-a457-ebc99fe4b46c
-- title:
--   Scheme Coh: is Regular Local Ring localization of smooth
-- statement:
--   The Scheme Coh construction uses the is Regular Local Ring localization of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L78-L82

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

theorem GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth (k A : Type*) [CommRing k] [IsRegularRing k]
    [CommRing A] [Algebra k A] [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by sorry
