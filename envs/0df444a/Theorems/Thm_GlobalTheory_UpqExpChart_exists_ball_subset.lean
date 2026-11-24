-- Prove2me | Theorems.Thm_GlobalTheory_UpqExpChart_exists_ball_subset
-- name    : GlobalTheory.UpqExpChart.exists_ball_subset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:46:51.550963+00:00
-- url     : https://prove2.me/theorems/377f0ea2-82fe-495d-8943-c56fb83efc82
-- title:
--   Upq Exp Chart: exists ball subset
-- statement:
--   The Upq Exp Chart construction uses the exists ball subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousMatExp.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousMatExp.lean#L28-L41

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
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
noncomputable section
open GlobalTheory GlobalTheory.UpqExpChart
variable {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.UpqExpChart.exists_ball_subset {W : Set (Matrix n n ℂ)} (hW : W ∈ 𝓝 (0 : Matrix n n ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Z : Matrix n n ℂ, ∑ i, ∑ j, ‖Z i j‖ < δ → Z ∈ W := by sorry
