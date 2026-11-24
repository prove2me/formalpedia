-- Prove2me | Theorems.Thm_GlobalTheory_VolPairExists_mat_injective
-- name    : GlobalTheory.VolPairExists.mat_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:56:10.480798+00:00
-- url     : https://prove2.me/theorems/e4096436-add4-41f8-a66a-54dfde0269ff
-- title:
--   Vol Pair Exists: mat injective
-- statement:
--   The Vol Pair Exists construction uses the mat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L90-L95

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

theorem GlobalTheory.VolPairExists.mat_injective : Function.Injective (UpqT.mat (P := P) (Q := Q)) := by sorry
