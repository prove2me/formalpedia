-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularRing_of_smooth_field
-- name    : GroundTheory.Arith.SchemeCoh.isRegularRing_of_smooth_field
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:37.690094+00:00
-- url     : https://prove2.me/theorems/3b3b358a-dedd-58b9-a076-8f5146a96492
-- title:
--   Scheme Coh: is Regular Ring of smooth field
-- statement:
--   The Scheme Coh construction uses the is Regular Ring of smooth field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L84-L86

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

theorem GroundTheory.Arith.SchemeCoh.isRegularRing_of_smooth_field (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : IsRegularRing A := by sorry
