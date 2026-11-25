-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_jW_er
-- name    : GlobalTheory.CompanionTheory.WedgeEmb.jW_er
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:00.744421+00:00
-- url     : https://prove2.me/theorems/7f5f291b-044e-43b9-a4c0-2f088a61b895
-- title:
--   Wedge Emb: j W er
-- statement:
--   The Wedge Emb construction uses the j W er property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L46-L55

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

theorem GlobalTheory.CompanionTheory.WedgeEmb.jW_er (I I' : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    jW n m (er I j, I.1.orderEmbOfFin I.2 j) I' = if I' = I then (-1) ^ (j : ℕ) else 0 := by sorry
