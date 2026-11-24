-- Prove2me | Theorems.Thm_GlobalTheory_SS_DefectZero_isSmoothAt_of_torsion_free
-- name    : GlobalTheory.SS.DefectZero.isSmoothAt_of_torsion_free
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:33:36.188367+00:00
-- url     : https://prove2.me/theorems/7e2d002e-0245-44fa-aeb8-efdfa6a1dd3c
-- title:
--   Defect Zero: is Smooth At of torsion free
-- statement:
--   The Defect Zero construction uses the is Smooth At of torsion free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L293-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L293-L352

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

theorem GlobalTheory.SS.DefectZero.isSmoothAt_of_torsion_free (R A B D : Type) [CommRing R] [IsRegularRing R] [CommRing A]
    [CommRing B] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [Algebra B D] [Algebra.FiniteType R A]
    [Algebra.FormallySmooth R A] [Module.Free A Ω[A⁄R]]
    (hs : Function.Surjective (algebraMap A B)) (q x : Ideal B) [q.IsPrime] [x.IsPrime]
    (hq : q = RingHom.ker (algebraMap B D))
    (hx : x = (IsLocalRing.maximalIdeal D).comap (algebraMap B D)) [Algebra.IsSmoothAt R q]
    (ht : ∀ w ∈ Submodule.torsion D (D ⊗[B] Ω[B⁄R]), w = 0) : Algebra.IsSmoothAt R x := by sorry
