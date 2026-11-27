-- Prove2me | Theorems.Thm_GlobalTheory_VolPairExists_read_iff
-- name    : GlobalTheory.VolPairExists.read_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:46.574913+00:00
-- url     : https://prove2.me/theorems/e1930cfc-7fc0-549a-96bf-b2d52ba05d58
-- title:
--   Vol Pair Exists: read iff
-- statement:
--   The Vol Pair Exists construction uses the read iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L194-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L194-L219

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
variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
variable {A A' : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} {L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ}

theorem GlobalTheory.VolPairExists.read_iff (hl : L * A = 1) (hr : A * L = 1) (u : UpqT P Q) (hu : UpqT.mat u = A' * L)
    {g : Matrix (Fin n) (Fin n) ℂ} (t : UpqT P Q) (ht : UpqT.mat t = A * g * L) (B : Set (UpqT P Q)) :
    (∃ b ∈ B, UpqT.mat b * A' = A' * g) ↔ t ∈ (fun b => b * u⁻¹) ⁻¹' ((fun b => u * b) ⁻¹' B) := by sorry
