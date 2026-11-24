-- Prove2me | Theorems.Thm_GlobalTheory_exists_int_bound_of_dual_eq_smul
-- name    : GlobalTheory.exists_int_bound_of_dual_eq_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:23.471628+00:00
-- url     : https://prove2.me/theorems/2bf4a8ac-c65d-4820-a5f4-7ac7233ae96d
-- title:
--   Global Theory: exists int bound of dual eq smul
-- statement:
--   The Global Theory construction uses the exists int bound of dual eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteUnitaryClassesOfDualEqSmul.lean#L96-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteUnitaryClassesOfDualEqSmul.lean#L96-L121

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

theorem GlobalTheory.exists_int_bound_of_dual_eq_smul (G : Matrix (Fin r) (Fin r) E)
    {c : FractionalIdeal (𝓞 E)⁰ E} (hc : c ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ Λ : Submodule (𝓞 E) (Fin r → E),
      (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ↔ x ∈ (c : Submodule (𝓞 E) E) • Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((N : E) * herm G x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) → (N : E) • x ∈ Λ := by sorry
