-- Prove2me | Theorems.Thm_GlobalTheory_VolPairExists_mat_mkU
-- name    : GlobalTheory.VolPairExists.mat_mkU
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:59.809265+00:00
-- url     : https://prove2.me/theorems/5da0198d-d46b-4fe7-aba5-add6c7978719
-- title:
--   Vol Pair Exists: mat mk U
-- statement:
--   The Vol Pair Exists construction uses the mat mk U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L88-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L88-L88

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

theorem GlobalTheory.VolPairExists.mat_mkU (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (h) : UpqT.mat (mkU u h) = u := by sorry
