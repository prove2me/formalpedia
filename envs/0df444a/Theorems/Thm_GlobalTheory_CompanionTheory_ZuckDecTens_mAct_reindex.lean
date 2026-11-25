-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckDecTens_mAct_reindex
-- name    : GlobalTheory.CompanionTheory.ZuckDecTens.mAct_reindex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:07:44.395523+00:00
-- url     : https://prove2.me/theorems/114099eb-493b-4b98-8b47-70080aab4515
-- title:
--   Zuck Dec Tens: m Act reindex
-- statement:
--   The Zuck Dec Tens construction uses the m Act reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTensorFromHomLaws.lean#L61-L64

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

theorem GlobalTheory.CompanionTheory.ZuckDecTens.mAct_reindex {ι ι' V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (e : ι' → ι) :
    (mAct ((1 : Matrix ι ι ℂ).submatrix e id) : (ι → V) →ₗ[ℂ] (ι' → V)) = LinearMap.funLeft ℂ V e := by sorry
