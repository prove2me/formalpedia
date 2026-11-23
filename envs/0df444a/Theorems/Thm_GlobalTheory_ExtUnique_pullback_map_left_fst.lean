-- Prove2me | Theorems.Thm_GlobalTheory_ExtUnique_pullback_map_left_fst
-- name    : GlobalTheory.ExtUnique.pullback_map_left_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:52.562104+00:00
-- url     : https://prove2.me/theorems/ce7ce4e9-2907-46d1-866f-e824dd66be5c
-- title:
--   Ext Unique: pullback map left fst
-- statement:
--   The Ext Unique construction uses the pullback map left fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L72-L74

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
omit [QuasiCompact j] [IsSchemeTheoreticallyDominant j]

theorem GlobalTheory.ExtUnique.pullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left := by sorry
