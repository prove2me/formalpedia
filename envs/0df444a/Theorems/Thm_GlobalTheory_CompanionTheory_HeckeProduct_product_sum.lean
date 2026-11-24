-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_product_sum
-- name    : GlobalTheory.CompanionTheory.HeckeProduct.product_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:59.564048+00:00
-- url     : https://prove2.me/theorems/1ce1d742-6da9-4725-83ca-df7388c18003
-- title:
--   Hecke Product: product sum
-- statement:
--   The Hecke Product construction uses the product sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L133-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L133-L161

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

theorem GlobalTheory.CompanionTheory.HeckeProduct.product_sum (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite)
    (hr : ∀ k ∈ K₁, ∀ g, f (g * k) = f g) (hr' : ∀ k ∈ K₂, ∀ g, f' (g * k) = f' g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f q.out.1 * f' q.out.2) • ρ q.out u
      = heckeSum (left ρ) K₁ f (heckeSum (right ρ) K₂ f' u) := by sorry
