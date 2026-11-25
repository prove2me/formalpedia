-- Prove2me | Theorems.Thm_GlobalTheory_StalkLimit_exists_lift_fromSpecStalk
-- name    : GlobalTheory.StalkLimit.exists_lift_fromSpecStalk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:20:14.044802+00:00
-- url     : https://prove2.me/theorems/fadff54d-3121-4d93-abef-6fca37fa5d14
-- title:
--   Stalk Limit: exists lift from Spec Stalk
-- statement:
--   The Stalk Limit construction uses the exists lift from Spec Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L18-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L18-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.StalkLimit
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.StalkLimit.exists_lift_fromSpecStalk {S T : Scheme.{u}} (x : S) (t : T ⟶ S)
    (ht : ∀ V : S.Opens, x ∈ V → ⊤ ≤ t ⁻¹ᵁ V) :
    ∃ l : T ⟶ Spec (S.presheaf.stalk x), l ≫ S.fromSpecStalk x = t := by sorry
