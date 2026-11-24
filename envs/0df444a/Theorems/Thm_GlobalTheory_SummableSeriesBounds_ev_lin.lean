-- Prove2me | Theorems.Thm_GlobalTheory_SummableSeriesBounds_ev_lin
-- name    : GlobalTheory.SummableSeriesBounds.ev_lin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:28.102526+00:00
-- url     : https://prove2.me/theorems/4b8e40f4-7b40-4d41-afc2-e276e96c9ca9
-- title:
--   Summable Series Bounds: ev lin
-- statement:
--   The Summable Series Bounds construction uses the ev lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L91-L98

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

theorem GlobalTheory.SummableSeriesBounds.ev_lin [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) : ev hπ (lin π) = 0 := by sorry
