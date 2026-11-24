-- Prove2me | Theorems.Thm_GlobalTheory_VolPairExists_conj_unitary
-- name    : GlobalTheory.VolPairExists.conj_unitary
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:55:54.184355+00:00
-- url     : https://prove2.me/theorems/0cc3bb7f-e250-401e-8649-565c506d2c72
-- title:
--   Vol Pair Exists: conj unitary
-- statement:
--   The Vol Pair Exists construction uses the conj unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L164-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L164-L170

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

theorem GlobalTheory.VolPairExists.conj_unitary (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ * G * g = G) : (A * g * L)ᴴ * Formalism.UG.Jpq P Q * (A * g * L) = Formalism.UG.Jpq P Q := by sorry
