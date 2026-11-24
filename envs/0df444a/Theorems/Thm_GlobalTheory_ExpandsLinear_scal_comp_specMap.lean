-- Prove2me | Theorems.Thm_GlobalTheory_ExpandsLinear_scal_comp_specMap
-- name    : GlobalTheory.ExpandsLinear.scal_comp_specMap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:07:51.454256+00:00
-- url     : https://prove2.me/theorems/e9442410-1ac4-4a52-934c-c8dfd1b7f45c
-- title:
--   Expands Linear: scal comp spec Map
-- statement:
--   The Expands Linear construction uses the scal comp spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ScalCompSpecMap.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ScalCompSpecMap.lean#L27-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ScalCompSpecMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ExpandsLinear

theorem GlobalTheory.ExpandsLinear.scal_comp_specMap {R C : Type} [CommRing R] [CommRing C] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (φ : R →+* C) (r : R) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by sorry
