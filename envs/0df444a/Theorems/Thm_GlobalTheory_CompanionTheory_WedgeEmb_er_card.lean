-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_er_card
-- name    : GlobalTheory.CompanionTheory.WedgeEmb.er_card
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:17.015479+00:00
-- url     : https://prove2.me/theorems/26d318b3-0d76-4712-b77c-388ca583e581
-- title:
--   Wedge Emb: er card
-- statement:
--   The Wedge Emb construction uses the er card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L30-L44

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

theorem GlobalTheory.CompanionTheory.WedgeEmb.er_card (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    ((er I j).1.filter fun a => a < I.1.orderEmbOfFin I.2 j).card = j := by sorry
