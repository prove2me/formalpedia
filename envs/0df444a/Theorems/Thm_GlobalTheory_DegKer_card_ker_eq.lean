-- Prove2me | Theorems.Thm_GlobalTheory_DegKer_card_ker_eq
-- name    : GlobalTheory.DegKer.card_ker_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:59:11.716805+00:00
-- url     : https://prove2.me/theorems/e3cf8676-adb5-4551-a86e-55c5967cecf1
-- title:
--   Deg Ker: card ker eq
-- statement:
--   The Deg Ker construction uses the card ker eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MapDegreeEqExpCharPowMulCardKernel.lean#L102-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MapDegreeEqExpCharPowMulCardKernel.lean#L102-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
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

theorem GlobalTheory.DegKer.card_ker_eq {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A]
    [LocallyOfFiniteType A.hom] (α : A ⟶ A) [IsMonHom α] [IsFinite α.left] (Ω : Type) [Field Ω]
    (s : Sp Ω ⟶ Sp K) :
    Nat.card {x : Out.baseOver (Sp K) ⟶ A // x ≫ α = 1} =
      Nat.card {y : Over.mk s ⟶ A // y ≫ α = 1} := by sorry
