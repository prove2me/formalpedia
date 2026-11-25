-- Prove2me | Theorems.Thm_GlobalTheory_EigenLieCompare_eigRank_eq
-- name    : GlobalTheory.EigenLieCompare.eigRank_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:43:26.42554+00:00
-- url     : https://prove2.me/theorems/34d08a2d-ffdc-411f-990a-29a9aa3c6d26
-- title:
--   Eigen Lie Compare: eig Rank eq
-- statement:
--   The Eigen Lie Compare construction uses the eig Rank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MulEqZeroOfToCompletion.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MulEqZeroOfToCompletion.lean#L125-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CotangentBidualToTangentFunctionInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MulEqZeroOfToCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.EigenLieCompare
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen GlobalTheory.HodgeTateCompare
open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems (Lie Cotangent)
variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
  [IsCommMonObj G] {R : Type} [CommRing R] (α : RingAct G R)

theorem GlobalTheory.EigenLieCompare.eigRank_eq (τ : R →+* O) :
    eigRank α τ = Module.finrank O (Module.Dual O (eigSub α τ)) := by sorry
