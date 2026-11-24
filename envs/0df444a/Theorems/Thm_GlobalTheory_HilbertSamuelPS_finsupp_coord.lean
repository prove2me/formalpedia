-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_finsupp_coord
-- name    : GlobalTheory.HilbertSamuelPS.finsupp_coord
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:21:41.743926+00:00
-- url     : https://prove2.me/theorems/224f8cb0-161e-41be-b66d-120e3f47a754
-- title:
--   Hilbert Samuel PS: finsupp coord
-- statement:
--   The Hilbert Samuel PS construction uses the finsupp coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L270-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L270-L272

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

theorem GlobalTheory.HilbertSamuelPS.finsupp_coord {D : ℕ} (e : Fin D →₀ ℕ) (a : Fin D → ℕ) (m : ℕ) (d : Fin D) :
    (m • e + ∑ d', Finsupp.single d' (a d')) d = m * e d + a d := by sorry
