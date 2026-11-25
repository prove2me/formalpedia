-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_support_product_quotient
-- name    : GlobalTheory.T.finite_support_product_quotient
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:07.624245+00:00
-- url     : https://prove2.me/theorems/9ef1c41e-d8d8-5460-93b8-d3a579b20820
-- title:
--   T: finite support product quotient
-- statement:
--   The T construction uses the finite support product quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportProductQuotientStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportProductQuotientStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportProductQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportProductQuotientStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_support_product_quotient : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ), (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite → (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite → (∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) → (∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) → (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by sorry
