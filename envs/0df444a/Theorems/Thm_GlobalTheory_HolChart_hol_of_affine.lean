-- Prove2me | Theorems.Thm_GlobalTheory_HolChart_hol_of_affine
-- name    : GlobalTheory.HolChart.hol_of_affine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:47.192701+00:00
-- url     : https://prove2.me/theorems/7462cc0f-1cee-4cfd-a172-c1ee6d1957da
-- title:
--   Hol Chart: hol of affine
-- statement:
--   The Hol Chart construction uses the hol of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEtaleCoordsVanishing.lean#L72-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEtaleCoordsVanishing.lean#L72-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
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
noncomputable section
open GlobalTheory GlobalTheory.HolChart

theorem GlobalTheory.HolChart.hol_of_affine
    (hval : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {g : ℕ} {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {W : Set (Fin g → ℂ)} (hW : IsOpen W)
    (s : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (hs : ∀ w ∈ W, ⊤ ≤ s w ⁻¹ᵁ U)
    (hd : ∀ a : Γ(X, U), DifferentiableOn ℂ (fun w => valAt' (s w) U a) W)
    (V : X.Opens) (f : Γ(X, V)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∧
      DifferentiableOn ℂ (fun w => valAt' (s w) V f) {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} := by sorry
