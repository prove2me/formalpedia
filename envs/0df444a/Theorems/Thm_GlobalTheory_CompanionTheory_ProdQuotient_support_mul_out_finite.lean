-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdQuotient_support_mul_out_finite
-- name    : GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:03.086386+00:00
-- url     : https://prove2.me/theorems/68b24505-f9c1-4885-9984-6e481abc5116
-- title:
--   Prod Quotient: support mul out finite
-- statement:
--   The Prod Quotient construction uses the support mul out finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportProductQuotient.lean#L7-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportProductQuotient.lean#L7-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportProductQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdQuotient

theorem GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁)
    (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (h₁ : (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite)
    (h₂ : (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite)
    (i₁ : ∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) (i₂ : ∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) :
    (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by sorry
