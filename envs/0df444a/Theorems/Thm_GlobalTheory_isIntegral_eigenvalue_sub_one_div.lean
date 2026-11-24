-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_eigenvalue_sub_one_div
-- name    : GlobalTheory.isIntegral_eigenvalue_sub_one_div
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:16.79753+00:00
-- url     : https://prove2.me/theorems/454e5fa6-9dd5-4a9f-b138-193e6a306450
-- title:
--   Global Theory: is Integral eigenvalue sub one div
-- statement:
--   The Global Theory construction uses the is Integral eigenvalue sub one div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RootOfUnityEqOneOfConjCongruence.lean#L9-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RootOfUnityEqOneOfConjCongruence.lean#L9-L61

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

theorem GlobalTheory.isIntegral_eigenvalue_sub_one_div {E : Type} [Field E] [NumberField E] {r M : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ)
    (hM : (M : ℂ) ≠ 0) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hγ : ∀ x ∈ Λ, ∃ y ∈ Λ, γ *ᵥ x - x = (M : E) • y)
    (w : Fin r → ℂ) (hw : w ≠ 0) (l : ℂ) (hl : w ᵥ* γ.map τ = l • w) :
    IsIntegral ℤ ((l - 1) / M) := by sorry
