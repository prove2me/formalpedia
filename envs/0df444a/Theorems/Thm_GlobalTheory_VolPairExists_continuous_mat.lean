-- Prove2me | Theorems.Thm_GlobalTheory_VolPairExists_continuous_mat
-- name    : GlobalTheory.VolPairExists.continuous_mat
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:50.514468+00:00
-- url     : https://prove2.me/theorems/6c10ff41-28eb-5667-8194-f298f5a8984c
-- title:
--   Vol Pair Exists: continuous mat
-- statement:
--   The Vol Pair Exists construction uses the continuous mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L105-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L105-L106

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.VolPairExists
variable {P Q : ℕ}

theorem GlobalTheory.VolPairExists.continuous_mat : Continuous (UpqT.mat (P := P) (Q := Q)) := by sorry
