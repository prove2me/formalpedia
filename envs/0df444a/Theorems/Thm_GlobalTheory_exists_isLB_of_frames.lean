-- Prove2me | Theorems.Thm_GlobalTheory_exists_isLB_of_frames
-- name    : GlobalTheory.exists_isLB_of_frames
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:58:02.226277+00:00
-- url     : https://prove2.me/theorems/88425ed6-f916-5666-8348-455b6cb6bb7f
-- title:
--   Global Theory: exists is LB of frames
-- statement:
--   The Global Theory construction uses the exists is LB of frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsMemThetaLevelCharApplyNeZero.lean#L52-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsMemThetaLevelCharApplyNeZero.lean#L52-L107

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMemThetaLevelCharApplyNeZero
import Theorems.Thm_GlobalTheory_IsSiegel_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.exists_isLB_of_frames (X : Over (Sp ℂ)) {Z κ : Type} (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (hex : Function.Surjective ex)
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X),
      ⊤ ≤ x.left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f')
    (U : κ → X.left.Opens) (hU : ⨆ i, U i = ⊤) (fr : κ → Z → ℂ)
    (hfr : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ U i → fr i z ≠ 0)
    (hreg : ∀ i j, ∃ φ : Γ(X.left, U i ⊓ U j), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ (U i ⊓ U j) →
      valAt' (ex z).left (U i ⊓ U j) φ = fr i z / fr j z) :
    ∃ tr : ∀ i j, Γ(X.left, U i ⊓ U j)ˣ, (LB.mk κ U tr).IsLB ∧ ∀ i j z,
      ⊤ ≤ (ex z).left ⁻¹ᵁ (U i ⊓ U j) →
        fr i z = valAt' (ex z).left (U i ⊓ U j) (tr i j).val * fr j z := by sorry
