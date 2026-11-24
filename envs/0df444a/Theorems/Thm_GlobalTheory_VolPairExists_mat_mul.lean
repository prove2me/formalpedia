-- Prove2me | Theorems.Thm_GlobalTheory_VolPairExists_mat_mul
-- name    : GlobalTheory.VolPairExists.mat_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:55:40.934802+00:00
-- url     : https://prove2.me/theorems/2dfc97c6-b99e-4a53-8e6a-4b594fbf499d
-- title:
--   Vol Pair Exists: mat mul
-- statement:
--   The Vol Pair Exists construction uses the mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L97-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L97-L97

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

theorem GlobalTheory.VolPairExists.mat_mul (b c : UpqT P Q) : UpqT.mat (b * c) = UpqT.mat b * UpqT.mat c := by sorry
