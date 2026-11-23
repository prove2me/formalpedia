-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularRing_of_smooth
-- name    : GroundTheory.Arith.SchemeCoh.isRegularRing_of_smooth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:44.447998+00:00
-- url     : https://prove2.me/theorems/fafb6ed7-44ea-4782-bb3d-408c30bff48f
-- title:
--   Scheme Coh: is Regular Ring of smooth
-- statement:
--   The Scheme Coh construction uses the is Regular Ring of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L52-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L52-L76

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

theorem GroundTheory.Arith.SchemeCoh.isRegularRing_of_smooth (k A : Type*) [CommRing k] [IsRegularRing k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsRegularRing A := by sorry
