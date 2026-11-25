-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_stalk_of_smooth_field
-- name    : GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:46.173742+00:00
-- url     : https://prove2.me/theorems/5fb4a146-ce1b-471d-8145-108c61d66a35
-- title:
--   Scheme Coh: is Regular Local Ring stalk of smooth field
-- statement:
--   The Scheme Coh construction uses the is Regular Local Ring stalk of smooth field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L112-L114

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

theorem GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by sorry
