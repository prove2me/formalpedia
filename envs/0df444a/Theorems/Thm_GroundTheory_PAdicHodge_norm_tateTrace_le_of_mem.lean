-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_tateTrace_le_of_mem
-- name    : GroundTheory.PAdicHodge.norm_tateTrace_le_of_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:19.725985+00:00
-- url     : https://prove2.me/theorems/b45dc076-b42e-4b14-b73c-ed0455b575ec
-- title:
--   PAdic Hodge: norm tate Trace le of mem
-- statement:
--   The PAdic Hodge construction uses the norm tate Trace le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L112-L114

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Module Set
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]
variable {K}

theorem GroundTheory.PAdicHodge.norm_tateTrace_le_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K,
    ‖tateTrace K n y‖ ≤ tateBound K * ‖y‖ := by sorry
