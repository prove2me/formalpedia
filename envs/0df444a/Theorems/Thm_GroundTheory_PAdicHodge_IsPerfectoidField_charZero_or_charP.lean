-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_charZero_or_charP
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.charZero_or_charP
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:11.822748+00:00
-- url     : https://prove2.me/theorems/15a0e7af-e8a1-4b0c-bcf5-fa235656bbe2
-- title:
--   Is Perfectoid Field: char Zero or char P
-- statement:
--   The Is Perfectoid Field construction uses the char Zero or char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCharP.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCharP.lean#L13-L38

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCharP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.charZero_or_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] :
    CharZero K ∨ CharP K p := by sorry
