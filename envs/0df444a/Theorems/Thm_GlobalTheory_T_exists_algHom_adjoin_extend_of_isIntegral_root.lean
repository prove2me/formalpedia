-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_algHom_adjoin_extend_of_isIntegral_root
-- name    : GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:27.421823+00:00
-- url     : https://prove2.me/theorems/bd06a84d-a2dc-4fb2-85d7-2b097e99d1a3
-- title:
--   T: exists alg Hom adjoin extend of is Integral root
-- statement:
--   The T construction uses the exists alg Hom adjoin extend of is Integral root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAlgHomAdjoinIntegralRootStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAlgHomAdjoinIntegralRootStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAlgHomAdjoinIntegralRoot
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAlgHomAdjoinIntegralRootStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ → ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 → ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω, ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))), ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by sorry
