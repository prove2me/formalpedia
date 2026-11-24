-- Prove2me | Theorems.Thm_GlobalTheory_GamFree_isOfFinOrder_of_bounded
-- name    : GlobalTheory.GamFree.isOfFinOrder_of_bounded
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:49:45.791568+00:00
-- url     : https://prove2.me/theorems/125adcbb-7dd0-4f52-818b-b14fab8f83dd
-- title:
--   Gam Free: is Of Fin Order of bounded
-- statement:
--   The Gam Free construction uses the is Of Fin Order of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOfFinOrderOfBounded.lean#L45-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOfFinOrderOfBounded.lean#L45-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GamFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E]

theorem GlobalTheory.GamFree.isOfFinOrder_of_bounded (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (γ : GL (Fin r) E)
    (hγ : ∀ v ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ Λ) (R : ℝ)
    (hR : ∀ (τ : Ψ) (k : ℕ) (a b : Fin r), ‖τ.1 (((γ : Matrix (Fin r) (Fin r) E) ^ k) a b)‖ ≤ R) :
    IsOfFinOrder γ := by sorry
