-- Prove2me | Theorems.Thm_GlobalTheory_KS_Sym_diff_prod
-- name    : GlobalTheory.KS.Sym.diff_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:27.302581+00:00
-- url     : https://prove2.me/theorems/1cbe36d5-4615-40b8-a618-3f3126444b24
-- title:
--   Sym: diff prod
-- statement:
--   The Sym construction uses the diff prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L352-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L352-L417

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
variable {K R : Type} [Field K] [CommRing R]

theorem GlobalTheory.KS.Sym.diff_prod {g : ℕ} (x₀ : R →+* K) {q : Y ⟶ Sp K} {s : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K}
    {W W' W'' : X.Opens} {d d' e : ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d)
    (hd' : LocDerK q s m D W' d') (he : LocDerK q s m D W'' e) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (hW'' : IsAffineOpen W'')
    {q₂ : Z ⟶ Sp K} {s₂ : X₂ ⟶ Sp R} {m₂ : Z ⟶ X₂} (sq₂ : m₂ ≫ s₂ = q₂ ≫ spMap x₀) {Q Q' Q₀ : X₂.Opens}
    {d₂ d₂' : ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Z, m₂ ⁻¹ᵁ O)} (hd₂ : LocDerK q₂ s₂ m₂ D Q d₂)
    (hd₂' : LocDerK q₂ s₂ m₂ D Q' d₂') {π π' : X₂ ⟶ X} {p p' : Z ⟶ Y}
    (sq : m₂ ≫ π = p ≫ m) (sq' : m₂ ≫ π' = p' ≫ m) (hQ : Q ≤ π ⁻¹ᵁ W) (hQ' : Q' ≤ π ⁻¹ᵁ W')
    (kQ : Q ≤ π' ⁻¹ᵁ W'') (kQ' : Q' ≤ π' ⁻¹ᵁ W'') (l : Q₀ ≤ Q) (l' : Q₀ ≤ Q')
    (c₁ : ∀ f : Γ(X, W), d₂ Q (pbT π f Q) = pbT p (d W f) _)
    (c₂ : ∀ f : Γ(X, W''), d₂ Q (pbT π' f Q) = pbT p' (e W'' f) _)
    (c₁' : ∀ f : Γ(X, W'), d₂' Q' (pbT π f Q') = pbT p (d' W' f) _)
    (c₂' : ∀ f : Γ(X, W''), d₂' Q' (pbT π' f Q') = pbT p' (e W'' f) _)
    (uniq : ∀ a b, LocDerK q₂ s₂ m₂ D Q₀ a → LocDerK q₂ s₂ m₂ D Q₀ b →
      (∀ f : Γ(X, W ⊓ W'), a Q₀ (pbT π f Q₀) = b Q₀ (pbT π f Q₀)) →
      (∀ f : Γ(X, W''), a Q₀ (pbT π' f Q₀) = b Q₀ (pbT π' f Q₀)) → ∀ O, O ≤ Q₀ → a O = b O)
    (θ : Fin g → Γ(Y, m ⁻¹ᵁ W ⊓ m ⁻¹ᵁ W')) {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hθ : ∀ f : Γ(X, W ⊓ W'), d' _ f - d _ f = ∑ a, rsT (θ a) _ * dd a _ ((m.app _).hom f))
    {w : Fin g → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hw : ∀ a, IsVF q₂ (w a))
    (w₁ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p ⁻¹ᵁ V → w a O (pbT p h O) = pbT p (dd a V h) O)
    (w₂ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p' ⁻¹ᵁ V → w a O (pbT p' h O) = 0)
    (O : X₂.Opens) (hO : O ≤ Q₀) (f : Γ(X₂, O)) :
    d₂' O f - d₂ O f = ∑ a, pbT p (θ a) _ * w a _ (pbT m₂ f _) := by sorry
