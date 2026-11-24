-- Prove2me | Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_cent_eq
-- name    : GlobalTheory.Tw.CentralizerAdjoin.cent_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:02:00.176627+00:00
-- url     : https://prove2.me/theorems/ee0fde56-3e25-45fe-84c5-0013f762ca8e
-- title:
--   Centralizer Adjoin: cent eq
-- statement:
--   The Centralizer Adjoin construction uses the cent eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L204-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L204-L232

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

theorem GlobalTheory.Tw.CentralizerAdjoin.cent_eq {δ : Matrix (Fin n) (Fin n) R} (hδ : Reg δ) :
    cent δ = {g | g ∈ Algebra.adjoin R {nrm δ} ∧ g * adj δ g = 1} := by sorry
