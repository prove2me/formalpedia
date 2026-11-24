-- Prove2me | Theorems.Thm_GlobalTheory_KS_exists_frame_on_family
-- name    : GlobalTheory.KS.exists_frame_on_family
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:47:51.587012+00:00
-- url     : https://prove2.me/theorems/c9ad386f-805a-4b09-8e0f-e944131f5df2
-- title:
--   KS: exists frame on family
-- statement:
--   The KS construction uses the exists frame on family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassIsSymmOfLift.lean#L48-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassIsSymmOfLift.lean#L48-L156

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

theorem GlobalTheory.KS.exists_frame_on_family (hL₀ : L₀.IsLB) (m : A₀.left ⟶ X) (L : LB X) (hL : L.IsLB)
    (hw : LBIso L₀ (L.pull m)) :
    ∃ a : L.ι → (Fin g → ℂ) → ℂ,
      (∀ i, DifferentiableOn ℂ (a i) (dom u m (L.U i)) ∧ ∀ z ∈ dom u m (L.U i), a i z ≠ 0) ∧
      (∀ i j, ∀ z ∈ dom u m (L.U i) ∩ dom u m (L.U j), a i z = fn u m _ (L.g i j).val z * a j z) ∧
      ∀ i (l : u.Λ) z (c : ℂ), z ∈ dom u m (L.U i) →
        (∀ b, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b → u.fr b z = c * u.fr b (z + l)) → a i z = c * a i (z + l) := by sorry
