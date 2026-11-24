-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_stalk_of_smooth
-- name    : GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:55.21192+00:00
-- url     : https://prove2.me/theorems/b6cf1afe-9735-48dc-8ba8-44bcb9b6b039
-- title:
--   Scheme Coh: is Regular Local Ring stalk of smooth
-- statement:
--   The Scheme Coh construction uses the is Regular Local Ring stalk of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L95-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L95-L110

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
open AlgebraicGeometry CategoryTheory

theorem GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth {X : Scheme.{u}} {R : CommRingCat.{u}} [IsRegularRing R]
    (f : X ⟶ Spec R) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by sorry
