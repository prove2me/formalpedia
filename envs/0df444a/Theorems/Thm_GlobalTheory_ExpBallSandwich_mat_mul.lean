-- Prove2me | Theorems.Thm_GlobalTheory_ExpBallSandwich_mat_mul
-- name    : GlobalTheory.ExpBallSandwich.mat_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:49.494648+00:00
-- url     : https://prove2.me/theorems/452a65fd-64d7-472a-94b5-4380087a8a08
-- title:
--   Exp Ball Sandwich: mat mul
-- statement:
--   The Exp Ball Sandwich construction uses the mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqExpLocalChart.lean#L125-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqExpLocalChart.lean#L125-L125

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

theorem GlobalTheory.ExpBallSandwich.mat_mul {P Q : ℕ} (g h : UpqT P Q) : UpqT.mat (g * h) = UpqT.mat g * UpqT.mat h := by sorry
