-- Prove2me | Theorems.Thm_GlobalTheory_ExtUnique_spec_fractionRing
-- name    : GlobalTheory.ExtUnique.spec_fractionRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:49.929247+00:00
-- url     : https://prove2.me/theorems/d9c19c99-ba2f-41d0-b5c0-1a647d46bfd3
-- title:
--   Ext Unique: spec fraction Ring
-- statement:
--   The Ext Unique construction uses the spec fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L35-L38

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

theorem GlobalTheory.ExtUnique.spec_fractionRing (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K] :
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by sorry
