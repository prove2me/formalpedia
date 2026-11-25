-- Prove2me | Theorems.Thm_GlobalTheory_CompactDualQuot_continuous_ptGauge
-- name    : GlobalTheory.CompactDualQuot.continuous_ptGauge
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:00:31.52651+00:00
-- url     : https://prove2.me/theorems/9d364b33-5683-4ed8-94b3-a50a9bc0d63b
-- title:
--   Compact Dual Quot: continuous pt Gauge
-- statement:
--   The Compact Dual Quot construction uses the continuous pt Gauge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContinuousMatrixEntryAbsSum.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContinuousMatrixEntryAbsSum.lean#L87-L89

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

theorem GlobalTheory.CompactDualQuot.continuous_ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (ptGauge e) := by sorry
