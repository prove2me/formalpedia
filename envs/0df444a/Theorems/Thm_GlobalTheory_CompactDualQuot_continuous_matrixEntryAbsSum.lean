-- Prove2me | Theorems.Thm_GlobalTheory_CompactDualQuot_continuous_matrixEntryAbsSum
-- name    : GlobalTheory.CompactDualQuot.continuous_matrixEntryAbsSum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:17:12.051482+00:00
-- url     : https://prove2.me/theorems/11700158-ebc6-4162-b8f5-68be9f36774d
-- title:
--   Compact Dual Quot: continuous matrix Entry Abs Sum
-- statement:
--   The Compact Dual Quot construction uses the continuous matrix Entry Abs Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContinuousMatrixEntryAbsSum.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContinuousMatrixEntryAbsSum.lean#L75-L77

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContinuousMatrixEntryAbsSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompactDualQuot
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal
variable {P Q P' Q' : ℕ}

theorem GlobalTheory.CompactDualQuot.continuous_matrixEntryAbsSum : Continuous (l1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → ℝ) := by sorry
