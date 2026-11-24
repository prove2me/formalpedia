-- Prove2me | Theorems.Thm_GlobalTheory_T_relIndex_open_compact_ne_zero
-- name    : GlobalTheory.T.relIndex_open_compact_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:29.25774+00:00
-- url     : https://prove2.me/theorems/00fc753e-6478-41dc-b8ea-27c62c2b4703
-- title:
--   T: rel Index open compact ne zero
-- statement:
--   The T construction uses the rel Index open compact ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RelIndexOpenCompactNeZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RelIndexOpenCompactNeZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexOpenCompactNeZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexOpenCompactNeZeroStatement
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

theorem GlobalTheory.T.relIndex_open_compact_ne_zero : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → H.relIndex A ≠ 0 := by sorry
