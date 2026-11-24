-- Prove2me | Theorems.Thm_GlobalTheory_SS_DefectZero_exists_smul_eq_zero
-- name    : GlobalTheory.SS.DefectZero.exists_smul_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:33:37.684+00:00
-- url     : https://prove2.me/theorems/dc9dc56f-455b-44f8-9166-4b280a516f8b
-- title:
--   Defect Zero: exists smul eq zero
-- statement:
--   The Defect Zero construction uses the exists smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L129-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L129-L145

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero

theorem GlobalTheory.SS.DefectZero.exists_smul_eq_zero (A K Q : Type) [CommRing A] [Field K] [Algebra A K] [AddCommGroup Q]
    [Module A Q] [Module.Finite A Q] [Subsingleton (K ⊗[A] Q)] (m : Q) :
    ∃ u : A, algebraMap A K u ≠ 0 ∧ u • m = 0 := by sorry
