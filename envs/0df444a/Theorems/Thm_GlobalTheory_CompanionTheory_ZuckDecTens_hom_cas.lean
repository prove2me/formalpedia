-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckDecTens_hom_cas
-- name    : GlobalTheory.CompanionTheory.ZuckDecTens.hom_cas
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:06.156013+00:00
-- url     : https://prove2.me/theorems/36f46fdc-bc75-408e-955e-a4f037755499
-- title:
--   Zuck Dec Tens: hom cas
-- statement:
--   The Zuck Dec Tens construction uses the hom cas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L75-L80

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

theorem GlobalTheory.CompanionTheory.ZuckDecTens.hom_cas (hL : HomLie) {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hX : X.1.OK) (hY : Y.1.OK) (hf : IsHom X Y f) :
    cas Y ∘ₗ f = f ∘ₗ cas X := by sorry
