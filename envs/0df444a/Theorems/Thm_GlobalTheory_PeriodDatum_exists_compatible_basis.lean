-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDatum_exists_compatible_basis
-- name    : GlobalTheory.PeriodDatum.exists_compatible_basis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:56:58.202661+00:00
-- url     : https://prove2.me/theorems/e863faff-9927-58ce-960f-1287870313cf
-- title:
--   Period Datum: exists compatible basis
-- statement:
--   The Period Datum construction uses the exists compatible basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsCompatibleBasis.lean#L55-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsCompatibleBasis.lean#L55-L80

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

theorem GlobalTheory.PeriodDatum.exists_compatible_basis (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (Γ : Type) [AddCommGroup Γ]
    (hdiv : ∀ x : Γ, ∃ y, p • y = x) (hcard : Nat.card {x : Γ // p • x = 0} = p ^ (2 * g)) :
    ∃ τ : Ix g → ℕ → Γ, (∀ i n, (p ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = p • τ i (n + 1)) ∧
      ∀ x : Γ, p • x = 0 → ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • τ j 0 := by sorry
