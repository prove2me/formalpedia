-- Prove2me | Theorems.Thm_GlobalTheory_SecLift_exists_liftIn_unfolded
-- name    : GlobalTheory.SecLift.exists_liftIn_unfolded
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:23.64384+00:00
-- url     : https://prove2.me/theorems/3da22474-cdc9-4675-89f3-895b1041383a
-- title:
--   Sec Lift: exists lift In unfolded
-- statement:
--   The Sec Lift construction uses the exists lift In unfolded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSectionLiftBasicOpenAffine.lean#L39-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSectionLiftBasicOpenAffine.lean#L39-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_FiniteLocalLifts_SmLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSectionLiftBasicOpenAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecLift
variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem GlobalTheory.SecLift.exists_liftIn_unfolded : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤ := by sorry
