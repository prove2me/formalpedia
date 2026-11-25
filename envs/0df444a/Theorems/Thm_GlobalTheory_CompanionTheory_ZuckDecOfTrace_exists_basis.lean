-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckDecOfTrace_exists_basis
-- name    : GlobalTheory.CompanionTheory.ZuckDecOfTrace.exists_basis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:26:26.37858+00:00
-- url     : https://prove2.me/theorems/c88753a6-7b84-4597-9e3e-73619707c162
-- title:
--   Zuck Dec Of Trace: exists basis
-- statement:
--   The Zuck Dec Of Trace construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTrace.lean#L34-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTrace.lean#L34-L94

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

theorem GlobalTheory.CompanionTheory.ZuckDecOfTrace.exists_basis (hc : IsLinCat N Hom) {P : Type} [DecidableEq P] {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr) (ν : P) :
    ∃ b : Module.Basis {k // par k = ν} ℂ (homSub hc (T ν) X),
      ∀ k, ∃ θ : N (T ν) →ₗ[ℂ] N (T (par k.1)), (b k).1 = io k.1 ∘ₗ θ := by sorry
