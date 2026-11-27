-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isDomain_stalk_of_smooth_field
-- name    : GroundTheory.Arith.SchemeCoh.isDomain_stalk_of_smooth_field
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:31.339371+00:00
-- url     : https://prove2.me/theorems/805db46f-51f4-55ab-8500-8b065bdffd5d
-- title:
--   Scheme Coh: is Domain stalk of smooth field
-- statement:
--   The Scheme Coh construction uses the is Domain stalk of smooth field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L116-L119

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

theorem GroundTheory.Arith.SchemeCoh.isDomain_stalk_of_smooth_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsDomain (X.presheaf.stalk x) := by sorry
