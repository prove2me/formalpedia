-- Prove2me | Theorems.Thm_GlobalTheory_ExpBallSandwich_sumAbs_mul_le
-- name    : GlobalTheory.ExpBallSandwich.sumAbs_mul_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:37.051154+00:00
-- url     : https://prove2.me/theorems/d3ceb7b2-5c58-4984-93ef-c45943d57494
-- title:
--   Exp Ball Sandwich: sum Abs mul le
-- statement:
--   The Exp Ball Sandwich construction uses the sum Abs mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqExpLocalChart.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqExpLocalChart.lean#L32-L39

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EntrySumMulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.ExpBallSandwich
variable {n : Type} [Fintype n] [DecidableEq n]
omit [DecidableEq n]

theorem GlobalTheory.ExpBallSandwich.sumAbs_mul_le (A B : Matrix n n ℂ) : sumAbs (A * B) ≤ sumAbs A * sumAbs B := by sorry
