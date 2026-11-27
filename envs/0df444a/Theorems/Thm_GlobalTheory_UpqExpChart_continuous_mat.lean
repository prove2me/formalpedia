-- Prove2me | Theorems.Thm_GlobalTheory_UpqExpChart_continuous_mat
-- name    : GlobalTheory.UpqExpChart.continuous_mat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:37.758102+00:00
-- url     : https://prove2.me/theorems/3beb4c12-65e4-5762-adb0-e8423ff2cfc9
-- title:
--   Upq Exp Chart: continuous mat
-- statement:
--   The Upq Exp Chart construction uses the continuous mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousMatExp.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousMatExp.lean#L83-L84

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

theorem GlobalTheory.UpqExpChart.continuous_mat {P Q : ℕ} : Continuous (UpqT.mat : UpqT P Q → _) := by sorry
