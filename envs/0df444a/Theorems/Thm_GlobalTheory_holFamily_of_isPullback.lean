-- Prove2me | Theorems.Thm_GlobalTheory_holFamily_of_isPullback
-- name    : GlobalTheory.holFamily_of_isPullback
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:55:41.640428+00:00
-- url     : https://prove2.me/theorems/ecfc84b7-c7c5-440e-8690-1828264bf320
-- title:
--   Global Theory: hol Family of is Pullback
-- statement:
--   The Global Theory construction uses the hol Family of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/HolFamilyOfIsPullback.lean#L68-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/HolFamilyOfIsPullback.lean#L68-L155

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.holFamily_of_isPullback
    (hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) {S X Y Z : Scheme.{0}} [IsAffine S]
    {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (H : IsPullback p q s t) (c : E → (Sp ℂ ⟶ Z))
    (ha : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w ≫ p) U f) {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U})
    (hb : ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w ≫ q) U f) {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U})
    (U : Z.Opens) (f : Γ(Z, U)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w) U f) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} := by sorry
