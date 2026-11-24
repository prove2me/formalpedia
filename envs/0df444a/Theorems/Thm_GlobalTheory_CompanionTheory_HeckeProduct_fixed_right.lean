-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_fixed_right
-- name    : GlobalTheory.CompanionTheory.HeckeProduct.fixed_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:28.802834+00:00
-- url     : https://prove2.me/theorems/a01f4f59-a926-4101-8d5e-a437ee5a6c84
-- title:
--   Hecke Product: fixed right
-- statement:
--   The Hecke Product construction uses the fixed right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L176-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L176-L186

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

theorem GlobalTheory.CompanionTheory.HeckeProduct.fixed_right (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite)
    (hl : ∀ k ∈ K₂, ∀ g, f' (k * g) = f' g) (hr : ∀ k ∈ K₂, ∀ g, f' (g * k) = f' g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∀ c ∈ K₁.prod K₂, ρ c (heckeSum (right ρ) K₂ f' u) = heckeSum (right ρ) K₂ f' u := by sorry
