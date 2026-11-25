-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bijective_app_of_isIso_morphismRestrict
-- name    : GroundTheory.Arith.SchemeCoh.bijective_app_of_isIso_morphismRestrict
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:16.39389+00:00
-- url     : https://prove2.me/theorems/5855d167-0824-5d2e-bd41-21e26ddaaeed
-- title:
--   Scheme Coh: bijective app of is Iso morphism Restrict
-- statement:
--   The Scheme Coh construction uses the bijective app of is Iso morphism Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/RestrictIso.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/RestrictIso.lean#L29-L41

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictIso
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
universe u
noncomputable section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem GroundTheory.Arith.SchemeCoh.bijective_app_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] {V : Y.Opens}
    (hV : V ≤ U) : Function.Bijective (f.app V) := by sorry
