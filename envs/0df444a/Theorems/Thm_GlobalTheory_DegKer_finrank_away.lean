-- Prove2me | Theorems.Thm_GlobalTheory_DegKer_finrank_away
-- name    : GlobalTheory.DegKer.finrank_away
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:20.731503+00:00
-- url     : https://prove2.me/theorems/4682d535-946f-4263-9a7f-ef8b8ca54d8d
-- title:
--   Deg Ker: finrank away
-- statement:
--   The Deg Ker construction uses the finrank away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MapDegreeEqExpCharPowMulCardKernel.lean#L149-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MapDegreeEqExpCharPowMulCardKernel.lean#L149-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_ZV_ActsBy_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open GlobalTheory.DegKer

theorem GlobalTheory.DegKer.finrank_away {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsDomain R] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] (f : R) (hf : f ≠ 0)
    [IsLocalization.Away f R'] [IsLocalization.Away (algebraMap R S f) S']
    (h : (algebraMap R' S').comp (algebraMap R R') = (algebraMap S S').comp (algebraMap R S)) :
    Module.finrank R' S' = Module.finrank R S := by sorry
