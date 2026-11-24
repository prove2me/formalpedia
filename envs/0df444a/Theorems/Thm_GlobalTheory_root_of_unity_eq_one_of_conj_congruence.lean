-- Prove2me | Theorems.Thm_GlobalTheory_root_of_unity_eq_one_of_conj_congruence
-- name    : GlobalTheory.root_of_unity_eq_one_of_conj_congruence
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:18.455188+00:00
-- url     : https://prove2.me/theorems/9d3c71e9-6b18-47cd-a191-08d750a8247c
-- title:
--   Global Theory: root of unity eq one of conj congruence
-- statement:
--   The Global Theory construction uses the root of unity eq one of conj congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RootOfUnityEqOneOfConjCongruence.lean#L88-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RootOfUnityEqOneOfConjCongruence.lean#L88-L119

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RootOfUnityEqOneOfConjCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory

theorem GlobalTheory.root_of_unity_eq_one_of_conj_congruence :
    ∀ (E : Type) [Field E] [NumberField E] (r M n : ℕ) (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (γ δ : Matrix (Fin r) (Fin r) E) (u : E) (τ : E →+* ℂ) (Q : Matrix (Fin r) (Fin r) ℂ), 0 < r → 3 ≤ M → 0 < n → u ^ n = 1 → Λ.FG → Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → (∀ x ∈ Λ', ∃ y ∈ Λ', Matrix.mulVec (δ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → Q.det ≠ 0 → (u • γ).map τ * Q = Q * δ.map τ → u = 1 := by sorry
