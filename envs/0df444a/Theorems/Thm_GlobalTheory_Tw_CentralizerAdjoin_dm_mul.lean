-- Prove2me | Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_dm_mul
-- name    : GlobalTheory.Tw.CentralizerAdjoin.dm_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:06.093812+00:00
-- url     : https://prove2.me/theorems/9be9f796-86eb-498f-a01c-a40133ae38c7
-- title:
--   Centralizer Adjoin: dm mul
-- statement:
--   The Centralizer Adjoin construction uses the dm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L28-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.CentralizerAdjoin
variable {n : ℕ} {R : Type} [CommRing R]

theorem GlobalTheory.Tw.CentralizerAdjoin.dm_mul (U V U' V' : Matrix (Fin n) (Fin n) R) :
    dm U V * dm U' V' = dm (U * U') (U * V' + V * U') := by sorry
