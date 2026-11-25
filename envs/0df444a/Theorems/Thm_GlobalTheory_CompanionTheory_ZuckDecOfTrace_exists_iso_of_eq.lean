-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckDecOfTrace_exists_iso_of_eq
-- name    : GlobalTheory.CompanionTheory.ZuckDecOfTrace.exists_iso_of_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:57.160782+00:00
-- url     : https://prove2.me/theorems/deaf05dc-9104-4070-ba26-f9dbef9caf10
-- title:
--   Zuck Dec Of Trace: exists iso of eq
-- statement:
--   The Zuck Dec Of Trace construction uses the exists iso of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTrace.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTrace.lean#L28-L32

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckDecOfTrace
universe u
variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}

theorem GlobalTheory.CompanionTheory.ZuckDecOfTrace.exists_iso_of_eq (hc : IsLinCat N Hom) {a b : O} (h : a = b) :
    ∃ (θ : N a →ₗ[ℂ] N b) (θ' : N b →ₗ[ℂ] N a), Hom a b θ ∧ Hom b a θ' ∧ θ ∘ₗ θ' = LinearMap.id ∧
      θ' ∘ₗ θ = LinearMap.id := by sorry
