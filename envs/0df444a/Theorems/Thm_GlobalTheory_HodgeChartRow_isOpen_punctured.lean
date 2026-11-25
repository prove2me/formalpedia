-- Prove2me | Theorems.Thm_GlobalTheory_HodgeChartRow_isOpen_punctured
-- name    : GlobalTheory.HodgeChartRow.isOpen_punctured
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:13.437871+00:00
-- url     : https://prove2.me/theorems/c9daa07f-fda6-4fbc-805f-b6dacf07e00e
-- title:
--   Hodge Chart Row: is Open punctured
-- statement:
--   The Hodge Chart Row construction uses the is Open punctured property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeChartBoundsOfSchurLemW.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeChartBoundsOfSchurLemW.lean#L34-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydiscStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernCurvatureFormSelfEqDualNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeChartBoundsOfSchurLemW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeChartRow

theorem GlobalTheory.HodgeChartRow.isOpen_punctured {n a : ℕ} (ha : a ≤ n) (ρ : ℝ) : IsOpen (punctured ha ρ) := by sorry
