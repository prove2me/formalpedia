-- Prove2me | Theorems.Thm_GlobalTheory_KS_ProdLift_finiteRing_sq_sub_mul_sq_eq_of_card
-- name    : GlobalTheory.KS.ProdLift.finiteRing_sq_sub_mul_sq_eq_of_card
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:51.983799+00:00
-- url     : https://prove2.me/theorems/61f80f89-fc4e-4229-868d-b505c17a8fe7
-- title:
--   Prod Lift: finite Ring sq sub mul sq eq of card
-- statement:
--   The Prod Lift construction uses the finite Ring sq sub mul sq eq of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L133-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L133-L196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.ProdLift

theorem GlobalTheory.KS.ProdLift.finiteRing_sq_sub_mul_sq_eq_of_card {K : Type} [Field K] {R : Type} [CommRing R] {Z Z₀ X Y : Scheme.{0}}
    {p q : Z ⟶ X} {s : X ⟶ Sp R} (H : IsPullback p q s s) {z : Z ⟶ Sp R} (hz : p ≫ s = z)
    {p₀ q₀ : Z₀ ⟶ Y} {s₀ : Y ⟶ Sp K} {z₀ : Z₀ ⟶ Sp K} (hp₀ : p₀ ≫ s₀ = z₀) (hq₀ : q₀ ≫ s₀ = z₀)
    {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z} (hp : m₂ ≫ p = p₀ ≫ m) (hq : m₂ ≫ q = q₀ ≫ m) (D : R → K)
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (Q : Z.Opens)
    (hQ : Q = p ⁻¹ᵁ W ⊓ q ⁻¹ᵁ W') :
    (∀ d d', LocDerK s₀ s m D W d → LocDerK s₀ s m D W' d' → ∃ d₂, LocDerK z₀ z m₂ D Q d₂ ∧
      (∀ f, d₂ Q (pbT p f Q) = pbT p₀ (d W f) _) ∧ ∀ f, d₂ Q (pbT q f Q) = pbT q₀ (d' W' f) _) ∧
    ∀ d₂ d₂', LocDerK z₀ z m₂ D Q d₂ → LocDerK z₀ z m₂ D Q d₂' →
      (∀ f : Γ(X, W), d₂ Q (pbT p f Q) = d₂' Q (pbT p f Q)) →
      (∀ f : Γ(X, W'), d₂ Q (pbT q f Q) = d₂' Q (pbT q f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by sorry
