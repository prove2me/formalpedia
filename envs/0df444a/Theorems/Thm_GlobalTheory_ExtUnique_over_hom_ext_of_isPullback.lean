-- Prove2me | Theorems.Thm_GlobalTheory_ExtUnique_over_hom_ext_of_isPullback
-- name    : GlobalTheory.ExtUnique.over_hom_ext_of_isPullback
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:56.267651+00:00
-- url     : https://prove2.me/theorems/771d5889-bc2a-4de4-97c1-1668060a59da
-- title:
--   Ext Unique: over hom ext of is Pullback
-- statement:
--   The Ext Unique construction uses the over hom ext of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L65-L69

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

theorem GlobalTheory.ExtUnique.over_hom_ext_of_isPullback {X Y : Over S} [Flat X.hom] [IsSeparated Y.hom] {X' : Scheme.{u}}
    {φ : X' ⟶ X.left} {p : X' ⟶ U} (h : IsPullback φ p X.hom j) {f g : X ⟶ Y}
    (hfg : φ ≫ f.left = φ ≫ g.left) : f = g := by sorry
