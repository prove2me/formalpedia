-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isDomain_localization_of_smooth
-- name    : GroundTheory.Arith.SchemeCoh.isDomain_localization_of_smooth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:23.976216+00:00
-- url     : https://prove2.me/theorems/8f1a92f1-98b1-5d13-a0a9-5aab78c89eab
-- title:
--   Scheme Coh: is Domain localization of smooth
-- statement:
--   The Scheme Coh construction uses the is Domain localization of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L88-L91

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

theorem GroundTheory.Arith.SchemeCoh.isDomain_localization_of_smooth (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] : IsDomain (Localization.AtPrime q) := by sorry
