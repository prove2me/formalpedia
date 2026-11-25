-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_first
-- name    : GlobalTheory.CompanionTheory.WedgeEmb.first
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:40.110846+00:00
-- url     : https://prove2.me/theorems/0c149515-08b5-4068-8801-e9999c5f0a70
-- title:
--   Wedge Emb: first
-- statement:
--   The Wedge Emb construction uses the first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L111-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L111-L149

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

theorem GlobalTheory.CompanionTheory.WedgeEmb.first (g : Matrix (Fin n) (Fin n) ℂ) : jW n m * cmp (m + 1) g = (cmp m g ⊗ₖ g) * jW n m := by sorry
