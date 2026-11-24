-- Prove2me | Theorems.Thm_GlobalTheory_finsum_doubleCoset_regroup
-- name    : GlobalTheory.finsum_doubleCoset_regroup
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:16.248529+00:00
-- url     : https://prove2.me/theorems/2a84e7dd-8c91-4471-9890-efbc39cbe6b8
-- title:
--   Global Theory: finsum double Coset regroup
-- statement:
--   The Global Theory construction uses the finsum double Coset regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumDoubleCosetRegroupCommutative.lean#L10-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumDoubleCosetRegroupCommutative.lean#L10-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumCompEqFinsumCardFiberMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardFiberDoubleCosetMapEqCardInfConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetRegroupCommutative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
open GlobalTheory

theorem GlobalTheory.finsum_doubleCoset_regroup (G : Type) [Group G] (T Γ C K' : Subgroup G) (φ : G → ℂ)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hCT : C ≤ T)
    (hU : ∀ x : G, T ⊓ K'.map (MulAut.conj x).toMonoidHom ≤ C ∧ (T ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0)
    (hφ : ∀ t ∈ T, ∀ k ∈ K', ∀ x, φ (t * x * k) = φ x) :
    ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G), ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) * ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K' : Set G), (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out q) := by sorry
