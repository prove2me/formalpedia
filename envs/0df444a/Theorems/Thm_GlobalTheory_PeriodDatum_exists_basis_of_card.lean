-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDatum_exists_basis_of_card
-- name    : GlobalTheory.PeriodDatum.exists_basis_of_card
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:18.346554+00:00
-- url     : https://prove2.me/theorems/d4f4b39d-f552-5f9c-85c8-58274708e391
-- title:
--   Period Datum: exists basis of card
-- statement:
--   The Period Datum construction uses the exists basis of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsCompatibleBasis.lean#L34-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsCompatibleBasis.lean#L34-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_DualLattices_SurjectiveAinfTowerZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TeichmullerQuot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DualTowerMapExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEndDifferentialRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicEndApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLiftOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfNaturalOnNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GroupLawPowerSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FiniteAlgebraSplitLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinEtaleFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsCompatibleBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PeriodDatum

theorem GlobalTheory.PeriodDatum.exists_basis_of_card (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (hcV : Nat.card V = p ^ (2 * g)) :
    ∃ f : Ix g → V, ∀ x : V, ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • f j := by sorry
