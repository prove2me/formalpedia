-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckDecTens_dec_comp
-- name    : GlobalTheory.CompanionTheory.ZuckDecTens.dec_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:10:28.726682+00:00
-- url     : https://prove2.me/theorems/02371fc9-8cfd-41ed-8417-f118d4eb77c8
-- title:
--   Zuck Dec Tens: dec comp
-- statement:
--   The Zuck Dec Tens construction uses the dec comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L17-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L17-L55

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfTensorFromHomLaws
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckDecTens
universe u
variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]

theorem GlobalTheory.CompanionTheory.ZuckDecTens.dec_comp {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop} (hc : IsLinCat N Hom) {A B P : Type} [Fintype A] [Fintype B]
    [Fintype P] (e : P ≃ A × B) {X : O} {Z : A → O} {S : A → B → O}
    {j : ∀ a, N (Z a) →ₗ[ℂ] N X} {q : ∀ a, N X →ₗ[ℂ] N (Z a)} (h : IsDec Hom X Z j q)
    {io : ∀ a b, N (S a b) →ₗ[ℂ] N (Z a)} {pr : ∀ a b, N (Z a) →ₗ[ℂ] N (S a b)}
    (h2 : ∀ a, IsDec Hom (Z a) (S a) (io a) (pr a)) :
    IsDec Hom X (fun p => S (e p).1 (e p).2) (fun p => j (e p).1 ∘ₗ io (e p).1 (e p).2)
      (fun p => pr (e p).1 (e p).2 ∘ₗ q (e p).1) := by sorry
