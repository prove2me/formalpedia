-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckTensHom_sum_list_comm
-- name    : GlobalTheory.CompanionTheory.ZuckTensHom.sum_list_comm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:03:22.652938+00:00
-- url     : https://prove2.me/theorems/2c23e4c3-8613-47d8-ba16-b5962b18b629
-- title:
--   Zuck Tens Hom: sum list comm
-- statement:
--   The Zuck Tens Hom construction uses the sum list comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L13-L17

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SnTens2
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckTensHom
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckTensHom.sum_list_comm {α β : Type} [Fintype β] (l : List α) (a : α → β → ℝ) :
    ∑ e, (l.map fun w => a w e).sum = (l.map fun w => ∑ e, a w e).sum := by sorry
