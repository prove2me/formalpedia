-- Prove2me | Theorems.Thm_GlobalTheory_ExtUnique_isSchemeTheoreticallyDominant_spec_of_injective
-- name    : GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:51.513167+00:00
-- url     : https://prove2.me/theorems/ff68f9b7-0530-45c7-acab-6e585fb91cd8
-- title:
--   Ext Unique: is Scheme Theoretically Dominant spec of injective
-- statement:
--   The Ext Unique construction uses the is Scheme Theoretically Dominant spec of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L25-L33

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

theorem GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by sorry
