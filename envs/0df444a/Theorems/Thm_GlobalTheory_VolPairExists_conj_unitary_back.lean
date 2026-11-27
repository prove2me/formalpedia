-- Prove2me | Theorems.Thm_GlobalTheory_VolPairExists_conj_unitary_back
-- name    : GlobalTheory.VolPairExists.conj_unitary_back
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:07.434275+00:00
-- url     : https://prove2.me/theorems/6eca3e14-4b9c-5365-9f77-b63f101cfc81
-- title:
--   Vol Pair Exists: conj unitary back
-- statement:
--   The Vol Pair Exists construction uses the conj unitary back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L172-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L172-L178

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

theorem GlobalTheory.VolPairExists.conj_unitary_back (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) (b : UpqT P Q) :
    (L * UpqT.mat b * A)ᴴ * G * (L * UpqT.mat b * A) = G := by sorry
