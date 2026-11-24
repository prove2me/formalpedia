-- Prove2me | Theorems.Thm_GlobalTheory_T_isCompact_sup_addSubgroup
-- name    : GlobalTheory.T.isCompact_sup_addSubgroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:21.391807+00:00
-- url     : https://prove2.me/theorems/0d8cdac0-d2d9-4001-9d67-2b7e54c253ec
-- title:
--   T: is Compact sup add Subgroup
-- statement:
--   The T construction uses the is Compact sup add Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsCompactSupAddSubgroupStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsCompactSupAddSubgroupStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactSupAddSubgroup
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactSupAddSubgroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isCompact_sup_addSubgroup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by sorry
