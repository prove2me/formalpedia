-- Prove2me | Theorems.Thm_GlobalTheory_SummableSeriesBounds_lin_dvd
-- name    : GlobalTheory.SummableSeriesBounds.lin_dvd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:50.288596+00:00
-- url     : https://prove2.me/theorems/02d7ee9a-0e96-40fd-97c9-13350c05cb48
-- title:
--   Summable Series Bounds: lin dvd
-- statement:
--   The Summable Series Bounds construction uses the lin dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L100-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L100-L135

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

theorem GlobalTheory.SummableSeriesBounds.lin_dvd [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) (h : ev hπ Φ = 0) :
    lin π ∣ Φ := by sorry
