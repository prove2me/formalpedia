-- Prove2me | Theorems.Thm_GlobalTheory_FrameUnits_val_eq_one_of_corr
-- name    : GlobalTheory.FrameUnits.val_eq_one_of_corr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:39:19.698805+00:00
-- url     : https://prove2.me/theorems/ddfb9b2e-b96a-4ff2-949b-5d099748b426
-- title:
--   Frame Units: val eq one of corr
-- statement:
--   The Frame Units construction uses the val eq one of corr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TripleProductTorusPeriodicBounded.lean#L231-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TripleProductTorusPeriodicBounded.lean#L231-L246

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem GlobalTheory.FrameUnits.val_eq_one_of_corr {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) (LB.oneGen L)) (x : Sp ℂ ⟶ Z) (j : L.ι)
    (hx : ∀ k, ⊤ ≤ ((x ≫ h) ≫ φ k) ⁻¹ᵁ L.U j) :
    valAt' (x ≫ h) (L.wchart φ fun _ => j) (t.s fun _ => j).val = 1 := by sorry
