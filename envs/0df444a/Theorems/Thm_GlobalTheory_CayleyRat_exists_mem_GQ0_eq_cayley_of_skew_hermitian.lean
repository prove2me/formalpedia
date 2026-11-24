-- Prove2me | Theorems.Thm_GlobalTheory_CayleyRat_exists_mem_GQ0_eq_cayley_of_skew_hermitian
-- name    : GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:33.665993+00:00
-- url     : https://prove2.me/theorems/e2817b40-1692-46dc-8226-ac00e481d7ed
-- title:
--   Cayley Rat: exists mem GQ0 eq cayley of skew hermitian
-- statement:
--   The Cayley Rat construction uses the exists mem GQ0 eq cayley of skew hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CayleyTransformMemRationalUnitaryGroup.lean#L7-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CayleyTransformMemRationalUnitaryGroup.lean#L7-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CayleyTransformMemRationalUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
open GlobalTheory GlobalTheory.CayleyRat

theorem GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by sorry
