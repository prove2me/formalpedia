-- Prove2me | Theorems.Thm_GlobalTheory_SS_DefectZero_isSmoothAt_iff_injective
-- name    : GlobalTheory.SS.DefectZero.isSmoothAt_iff_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:28.460879+00:00
-- url     : https://prove2.me/theorems/e1a12dda-888f-4ce7-ac4c-959c4173dbbe
-- title:
--   Defect Zero: is Smooth At iff injective
-- statement:
--   The Defect Zero construction uses the is Smooth At iff injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L18-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L18-L84

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

theorem GlobalTheory.SS.DefectZero.isSmoothAt_iff_injective (R A B K : Type) [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] [IsNoetherianRing A] [Algebra.FormallySmooth R A]
    [Module.Free A Ω[A⁄R]] [Module.Finite A Ω[A⁄R]] (hs : Function.Surjective (algebraMap A B))
    (q : Ideal B) [q.IsPrime] (hq : q = RingHom.ker (algebraMap B K)) :
    Algebra.IsSmoothAt R q ↔ Function.Injective (cotangentComplexBaseChange R B A K) := by sorry
