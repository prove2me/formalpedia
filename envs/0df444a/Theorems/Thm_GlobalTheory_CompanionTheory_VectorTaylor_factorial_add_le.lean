-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VectorTaylor_factorial_add_le
-- name    : GlobalTheory.CompanionTheory.VectorTaylor.factorial_add_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:36.72109+00:00
-- url     : https://prove2.me/theorems/a76554db-770a-47fc-81ca-e0219408add2
-- title:
--   Vector Taylor: factorial add le
-- statement:
--   The Vector Taylor construction uses the factorial add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticOrthogonalVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VectorTaylor
open Filter Topology

theorem GlobalTheory.CompanionTheory.VectorTaylor.factorial_add_le (k n : ℕ) :
    ((k + n).factorial : ℝ) ≤ 2 ^ (k + n) * k.factorial * n.factorial := by sorry
