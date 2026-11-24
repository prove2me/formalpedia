-- Prove2me | Theorems.Thm_GlobalTheory_UpqExpChart_continuous_matExp
-- name    : GlobalTheory.UpqExpChart.continuous_matExp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:42:27.818574+00:00
-- url     : https://prove2.me/theorems/0df48386-893e-417b-bc54-9e252135a4ae
-- title:
--   Upq Exp Chart: continuous mat Exp
-- statement:
--   The Upq Exp Chart construction uses the continuous mat Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousMatExp.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousMatExp.lean#L14-L16

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

theorem GlobalTheory.UpqExpChart.continuous_matExp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by sorry
