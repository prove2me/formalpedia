-- Prove2me | Theorems.Thm_GlobalTheory_SummableSeriesBounds_lin_ne_zero
-- name    : GlobalTheory.SummableSeriesBounds.lin_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:52.704211+00:00
-- url     : https://prove2.me/theorems/70254ae9-ba4e-4bfb-8d37-f281a8df70a9
-- title:
--   Summable Series Bounds: lin ne zero
-- statement:
--   The Summable Series Bounds construction uses the lin ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L86-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem GlobalTheory.SummableSeriesBounds.lin_ne_zero (π : C) : lin π ≠ 0 := by sorry
