-- Prove2me | Theorems.Thm_GlobalTheory_KS_PtDer_log_cocycle
-- name    : GlobalTheory.KS.PtDer.log_cocycle
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:00:56.608985+00:00
-- url     : https://prove2.me/theorems/15f98bec-cadf-47a6-953b-f0e8135cb305
-- title:
--   Pt Der: log cocycle
-- statement:
--   The Pt Der construction uses the log cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassIsSymmOfLift.lean#L179-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassIsSymmOfLift.lean#L179-L199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassIsSymmOfLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem GlobalTheory.KS.PtDer.log_cocycle {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) {L : LB X} (hL : L.IsLB)
    (i j k : L.ι) (hi : ⊤ ≤ y ⁻¹ᵁ L.U i) (hj : ⊤ ≤ y ⁻¹ᵁ L.U j) (hk : ⊤ ≤ y ⁻¹ᵁ L.U k) :
    δ _ (L.g i j).val / valAt' y _ (L.g i j).val + δ _ (L.g j k).val / valAt' y _ (L.g j k).val =
      δ _ (L.g i k).val / valAt' y _ (L.g i k).val := by sorry
