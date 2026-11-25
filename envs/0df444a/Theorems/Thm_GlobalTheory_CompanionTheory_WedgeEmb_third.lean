-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_third
-- name    : GlobalTheory.CompanionTheory.WedgeEmb.third
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:07.858713+00:00
-- url     : https://prove2.me/theorems/7cb7c48f-5958-59b0-815f-50da118ca020
-- title:
--   Wedge Emb: third
-- statement:
--   The Wedge Emb construction uses the third property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L156-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L156-L174

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

theorem GlobalTheory.CompanionTheory.WedgeEmb.third : (jW n m)ᵀ * jW n m = ((m : ℂ) + 1) • (1 : Matrix (BranchingSupport.Sub n (m + 1)) (BranchingSupport.Sub n (m + 1)) ℂ) := by sorry
