-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_cmp_tr
-- name    : GlobalTheory.CompanionTheory.WedgeEmb.cmp_tr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:01.522307+00:00
-- url     : https://prove2.me/theorems/5d91a453-56c6-5028-b774-aa21dc82536d
-- title:
--   Wedge Emb: cmp tr
-- statement:
--   The Wedge Emb construction uses the cmp tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L151-L154

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeEmb
variable {n m : ℕ}

theorem GlobalTheory.CompanionTheory.WedgeEmb.cmp_tr (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : BranchingSupport.cmp l gᵀ = (BranchingSupport.cmp l g)ᵀ := by sorry
