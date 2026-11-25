-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_wedgeInt
-- name    : GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:23:47.257476+00:00
-- url     : https://prove2.me/theorems/676d1f8e-b443-52ab-b1d0-ced35bcf4488
-- title:
--   Wedge Emb: wedge Int
-- statement:
--   The Wedge Emb construction uses the wedge Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L176-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L176-L182

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

theorem GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt : WedgeInt := by sorry
