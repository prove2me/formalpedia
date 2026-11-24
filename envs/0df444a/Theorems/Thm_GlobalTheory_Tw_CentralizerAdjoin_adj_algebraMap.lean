-- Prove2me | Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_algebraMap
-- name    : GlobalTheory.Tw.CentralizerAdjoin.adj_algebraMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:02:28.41092+00:00
-- url     : https://prove2.me/theorems/8bfd2d4e-c99d-4640-ad4f-6c3e1d217b58
-- title:
--   Centralizer Adjoin: adj algebra Map
-- statement:
--   The Centralizer Adjoin construction uses the adj algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L137-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L137-L143

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
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model

theorem GlobalTheory.Tw.CentralizerAdjoin.adj_algebraMap {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (r : R) :
    adj δ (algebraMap R _ r) = algebraMap R _ (star r) := by sorry
