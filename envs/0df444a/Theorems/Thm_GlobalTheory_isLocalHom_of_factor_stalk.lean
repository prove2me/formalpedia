-- Prove2me | Theorems.Thm_GlobalTheory_isLocalHom_of_factor_stalk
-- name    : GlobalTheory.isLocalHom_of_factor_stalk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:19.986514+00:00
-- url     : https://prove2.me/theorems/7d08157b-1ca0-483b-8c1e-db4265b665a4
-- title:
--   Global Theory: is Local Hom of factor stalk
-- statement:
--   The Global Theory construction uses the is Local Hom of factor stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L119-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}

theorem GlobalTheory.isLocalHom_of_factor_stalk {f : Spec (.of R) ⟶ X} {x : X} (hx : f (closedPoint R) = x)
    {φ : X.presheaf.stalk x ⟶ .of R} (hφ : Spec.map φ ≫ X.fromSpecStalk x = f) :
    IsLocalHom φ.hom := by sorry
