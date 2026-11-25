-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckDecOfTrace_dec_of_gen
-- name    : GlobalTheory.CompanionTheory.ZuckDecOfTrace.dec_of_gen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:59:19.85294+00:00
-- url     : https://prove2.me/theorems/a0347359-48ee-4379-9b51-e2c54a0bfdb1
-- title:
--   Zuck Dec Of Trace: dec of gen
-- statement:
--   The Zuck Dec Of Trace construction uses the dec of gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTrace.lean#L119-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTrace.lean#L119-L179

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

theorem GlobalTheory.CompanionTheory.ZuckDecOfTrace.dec_of_gen (hc : IsLinCat N Hom) {P : Type} {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X Z : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr)
    {j : N Z →ₗ[ℂ] N X} {q : N X →ₗ[ℂ] N Z} (hj : Hom Z X j) (hq : Hom X Z q) (hqj : q ∘ₗ j = LinearMap.id)
    {I : Type} [Fintype I] {e : I → P} (he : Function.Injective e)
    (g : ∀ i, homSub hc (T (e i)) Z) (hg0 : ∀ i, g i ≠ 0) (hg : ∀ i w, ∃ c : ℂ, c • g i = w)
    (h0 : ∀ ν, (∀ i, e i ≠ ν) → ∀ w : homSub hc (T ν) Z, w = 0) :
    ∃ io pr, IsDec Hom Z (fun i => T (e i)) io pr := by sorry
