-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_nat_mul_add_inj
-- name    : GlobalTheory.HilbertSamuelPS.nat_mul_add_inj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:21:34.860521+00:00
-- url     : https://prove2.me/theorems/27b80e81-8051-47fa-8d69-d94aeece04f8
-- title:
--   Hilbert Samuel PS: nat mul add inj
-- statement:
--   The Hilbert Samuel PS construction uses the nat mul add inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L261-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L261-L268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries

theorem GlobalTheory.HilbertSamuelPS.nat_mul_add_inj {m x y x' y' : ℕ} (hy : y < m) (hy' : y' < m)
    (h : m * x + y = m * x' + y') : x = x' ∧ y = y' := by sorry
