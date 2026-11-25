-- Prove2me | Theorems.Thm_GlobalTheory_EigenLieCompare_mem_jacobson
-- name    : GlobalTheory.EigenLieCompare.mem_jacobson
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:43:02.070061+00:00
-- url     : https://prove2.me/theorems/b1c0c83f-7e04-4f21-9f61-f2932b933d11
-- title:
--   Eigen Lie Compare: mem jacobson
-- statement:
--   The Eigen Lie Compare construction uses the mem jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MulEqZeroOfToCompletion.lean#L267-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MulEqZeroOfToCompletion.lean#L267-L276

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
variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.EigenLieCompare.mem_jacobson {x : PadicOrder p E} (hx : ∀ w, IsOver p w → x ∈ plId p w) :
    x ∈ (⊥ : Ideal (PadicOrder p E)).jacobson := by sorry
