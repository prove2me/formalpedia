-- Prove2me | Theorems.Thm_GlobalTheory_CompactDualQuot_sg_ne_zero
-- name    : GlobalTheory.CompactDualQuot.sg_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:08.091807+00:00
-- url     : https://prove2.me/theorems/1eb2a353-12c7-582d-bcb8-61474ff4aadc
-- title:
--   Compact Dual Quot: sg ne zero
-- statement:
--   The Compact Dual Quot construction uses the sg ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContinuousMatrixEntryAbsSum.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContinuousMatrixEntryAbsSum.lean#L47-L48

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

theorem GlobalTheory.CompactDualQuot.sg_ne_zero (i : Fin P ⊕ Fin Q) : sg i ≠ 0 := by sorry
