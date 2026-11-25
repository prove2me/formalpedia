-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_sum_jW
-- name    : GlobalTheory.CompanionTheory.WedgeEmb.sum_jW
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:23:37.239259+00:00
-- url     : https://prove2.me/theorems/a0981329-eff6-5067-80ed-1657a55c9e21
-- title:
--   Wedge Emb: sum j W
-- statement:
--   The Wedge Emb construction uses the sum j W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L74-L86

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

theorem GlobalTheory.CompanionTheory.WedgeEmb.sum_jW (F : BranchingSupport.Sub n m × Fin n → ℂ) (I : BranchingSupport.Sub n (m + 1)) :
    ∑ p, F p * jW n m p I = ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * F (er I j, I.1.orderEmbOfFin I.2 j) := by sorry
