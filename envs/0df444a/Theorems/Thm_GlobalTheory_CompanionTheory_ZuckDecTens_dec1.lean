-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckDecTens_dec1
-- name    : GlobalTheory.CompanionTheory.ZuckDecTens.dec1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:01:17.239741+00:00
-- url     : https://prove2.me/theorems/fe97eb1a-bbc1-5212-b97e-7a027a3c1ad4
-- title:
--   Zuck Dec Tens: dec1
-- statement:
--   The Zuck Dec Tens construction uses the dec1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L82-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L82-L106

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
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckDecTens.dec1 (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F, U)} {pr : ∀ a, M (F, U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F, U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F', T a))
      (fun a => on1 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.snd : Unit × F'.ι → F'.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F'.ι => ((), c)) ∘ₗ on1 (pr a)) := by sorry
