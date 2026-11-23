-- Prove2me | Theorems.Thm_GlobalTheory_ExtUnique_hom_ext_of_dominant
-- name    : GlobalTheory.ExtUnique.hom_ext_of_dominant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:31.123769+00:00
-- url     : https://prove2.me/theorems/75a7b71f-2330-4b52-9df1-2fa65dad944c
-- title:
--   Ext Unique: hom ext of dominant
-- statement:
--   The Ext Unique construction uses the hom ext of dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L40-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L40-L59

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

theorem GlobalTheory.ExtUnique.hom_ext_of_dominant {W X Y Z : Scheme.{u}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) (w : W ⟶ X) [IsSchemeTheoreticallyDominant w] (hw : w ≫ f = w ≫ g) : f = g := by sorry
