-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_unitary_classes
-- name    : GlobalTheory.exists_finite_unitary_classes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:11.594089+00:00
-- url     : https://prove2.me/theorems/41858643-247a-4c40-898e-3b3995c8212c
-- title:
--   Global Theory: exists finite unitary classes
-- statement:
--   The Global Theory construction uses the exists finite unitary classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteUnitaryClassesOfDualEqSmul.lean#L42-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteUnitaryClassesOfDualEqSmul.lean#L42-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteUnitaryClassesOfDualEqSmul_87ddafdad67ddc06
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.exists_finite_unitary_classes (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0) {N : ℤ} (hN : N ≠ 0)
    {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) {α : Type*} {ι : Type*} [Finite ι]
    (Λ : α → Submodule (𝓞 E) (Fin r → E)) (t : α → ι → Fin r → E)
    (hΛ : ∀ a, IsLattice (Λ a))
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ ((N : E) * herm G x y))
    (hdual : ∀ a x, (∀ y ∈ Λ a, IsIntegral ℤ (herm G x y)) → (N : E) • x ∈ Λ a)
    (ht : ∀ a i, t a i ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : GL (Fin r) E,
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
        herm G x y) ∧
      (∀ x, x ∈ Λ a ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ s) ∧
      ∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ t a i - t s i ∈ 𝔪 • Λ s := by sorry
