-- Prove2me | Theorems.Thm_GlobalTheory_ExtUnique_existsUnique_oAct_of_isGrpPullback
-- name    : GlobalTheory.ExtUnique.existsUnique_oAct_of_isGrpPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:34.731831+00:00
-- url     : https://prove2.me/theorems/ac092c07-579e-4884-883b-d04cf04560f7
-- title:
--   Ext Unique: exists Unique o Act of is Grp Pullback
-- statement:
--   The Ext Unique construction uses the exists Unique o Act of is Grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L170-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L170-L188

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
variable {U S : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]

theorem GlobalTheory.ExtUnique.existsUnique_oAct_of_isGrpPullback {O : Type} [CommRing O] {G : Over S} [GrpObj G] [Flat G.hom]
    [IsSeparated G.hom] {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G j φ)
    (i : OAct O G') (hi : ∀ x, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) :
    ∃! a : OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by sorry
