-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_sum_left_right_comm
-- name    : GlobalTheory.CompanionTheory.HeckeProduct.sum_left_right_comm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:54.432295+00:00
-- url     : https://prove2.me/theorems/e470bb19-e1d7-466d-ad05-018f87c1422b
-- title:
--   Hecke Product: sum left right comm
-- statement:
--   The Hecke Product construction uses the sum left right comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L124-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeProduct
variable {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
variable {f : G₁ → ℂ} {f' : G₂ → ℂ}

theorem GlobalTheory.CompanionTheory.HeckeProduct.sum_left_right_comm (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite) (u : V) :
    heckeSum (left ρ) K₁ f (heckeSum (right ρ) K₂ f' u)
      = heckeSum (right ρ) K₂ f' (heckeSum (left ρ) K₁ f u) := by sorry
