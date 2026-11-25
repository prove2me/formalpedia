-- Prove2me | Theorems.Thm_GlobalTheory_ExpBallSandwich_defect_le
-- name    : GlobalTheory.ExpBallSandwich.defect_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:13:05.063405+00:00
-- url     : https://prove2.me/theorems/085f0e8c-0ec0-5943-9aa3-621e5b5e6656
-- title:
--   Exp Ball Sandwich: defect le
-- statement:
--   The Exp Ball Sandwich construction uses the defect le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqExpLocalChart.lean#L88-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqExpLocalChart.lean#L88-L121

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

theorem GlobalTheory.ExpBallSandwich.defect_le (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ X Y Z : Matrix n n ℂ,
    sumAbs X < ρ → sumAbs Y < ρ → sumAbs Z < ρ →
    NormedSpace.exp Y = NormedSpace.exp X * NormedSpace.exp Z →
    sumAbs (Y - X - Z) ≤ η * sumAbs (Y - X) + 3 * η * sumAbs Z := by sorry
