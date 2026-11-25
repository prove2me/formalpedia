-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_er_emb
-- name    : GlobalTheory.CompanionTheory.WedgeEmb.er_emb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:06:17.393775+00:00
-- url     : https://prove2.me/theorems/3bf1851e-b552-41d4-bd9d-2d5c344d292c
-- title:
--   Wedge Emb: er emb
-- statement:
--   The Wedge Emb construction uses the er emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L14-L22

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

theorem GlobalTheory.CompanionTheory.WedgeEmb.er_emb (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    ⇑((er I j).1.orderEmbOfFin (er I j).2) = fun a => I.1.orderEmbOfFin I.2 (j.succAbove a) := by sorry
