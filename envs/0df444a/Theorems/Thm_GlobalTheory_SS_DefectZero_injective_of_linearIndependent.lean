-- Prove2me | Theorems.Thm_GlobalTheory_SS_DefectZero_injective_of_linearIndependent
-- name    : GlobalTheory.SS.DefectZero.injective_of_linearIndependent
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:33:40.60129+00:00
-- url     : https://prove2.me/theorems/1999e0bc-adcc-4c55-8be2-ba584e8533c4
-- title:
--   Defect Zero: injective of linear Independent
-- statement:
--   The Defect Zero construction uses the injective of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L280-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L280-L291

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

theorem GlobalTheory.SS.DefectZero.injective_of_linearIndependent (R A C k I : Type) [CommRing R] [CommRing A] [CommRing C]
    [Field k] [Algebra R A] [Algebra A C] [Algebra C k] [Algebra A k] [IsScalarTower A C k]
    (f : I → A) (hf : RingHom.ker (algebraMap A C) = Ideal.span (Set.range f))
    (hl : LinearIndependent k fun j => (1 : k) ⊗ₜ[A] KaehlerDifferential.D R A (f j)) :
    Function.Injective (cotangentComplexBaseChange R C A k) := by sorry
