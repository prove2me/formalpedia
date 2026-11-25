-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckDecTens_hom_reindex
-- name    : GlobalTheory.CompanionTheory.ZuckDecTens.hom_reindex
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:00:03.311553+00:00
-- url     : https://prove2.me/theorems/0fe54324-80f2-549b-bc60-02d933f5f9e1
-- title:
--   Zuck Dec Tens: hom reindex
-- statement:
--   The Zuck Dec Tens construction uses the hom reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L66-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L66-L73

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

theorem GlobalTheory.CompanionTheory.ZuckDecTens.hom_reindex (hM : MatHom) (F F' : FRep k r) (U : URep k r) (e : F'.ι ≃ F.ι)
    (h : ∀ g, F'.ρ g = (F.ρ g).submatrix e e) :
    IsHom (F, U) (F', U) (LinearMap.funLeft ℂ U.R.smSub e) := by sorry
