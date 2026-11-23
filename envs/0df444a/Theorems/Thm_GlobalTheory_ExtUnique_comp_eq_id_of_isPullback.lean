-- Prove2me | Theorems.Thm_GlobalTheory_ExtUnique_comp_eq_id_of_isPullback
-- name    : GlobalTheory.ExtUnique.comp_eq_id_of_isPullback
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:41.66255+00:00
-- url     : https://prove2.me/theorems/be37eb17-e31b-4b84-949c-e2fde479c054
-- title:
--   Ext Unique: comp eq id of is Pullback
-- statement:
--   The Ext Unique construction uses the comp eq id of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L94-L105

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
variable {U S : Scheme.{u}} (j : U ⟶ S) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
variable {j}

theorem GlobalTheory.ExtUnique.comp_eq_id_of_isPullback {X Y : Over S} [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom]
    {X' Y' : Over U} {φ : X'.left ⟶ X.left} {ψ : Y'.left ⟶ Y.left}
    (hX : IsPullback φ X'.hom X.hom j) (hY : IsPullback ψ Y'.hom Y.hom j) (e : X' ≅ Y') (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : e.hom.left ≫ ψ = φ ≫ f.left) (hg : e.inv.left ≫ φ = ψ ≫ g.left) :
    f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y := by sorry
