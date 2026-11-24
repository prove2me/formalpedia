-- Prove2me | Theorems.Thm_GlobalTheory_exists_forms_idealOfVars_le_radical
-- name    : GlobalTheory.exists_forms_idealOfVars_le_radical
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:29.036679+00:00
-- url     : https://prove2.me/theorems/02af29c5-181c-47ca-9a8e-c373e3a8d9ba
-- title:
--   Global Theory: exists forms ideal Of Vars le radical
-- statement:
--   The Global Theory construction uses the exists forms ideal Of Vars le radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L148-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L148-L206

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ : Type*}
variable [Finite σ] {k : Type*} [Field k]

theorem GlobalTheory.exists_forms_idealOfVars_le_radical (n : ℕ) :
    ∀ (J : Ideal (MvPolynomial σ k)), J.IsHomogeneous (homogeneousSubmodule σ k) → J ≠ ⊤ →
      ringKrullDim (MvPolynomial σ k ⧸ J) ≤ n →
      ∃ e, 0 < e ∧ ∃ F : Fin n → MvPolynomial σ k, (∀ i, (F i).IsHomogeneous e) ∧
        idealOfVars σ k ≤ (J ⊔ Ideal.span (Set.range F)).radical := by sorry
