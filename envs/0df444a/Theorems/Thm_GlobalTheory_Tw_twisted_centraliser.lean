-- Prove2me | Theorems.Thm_GlobalTheory_Tw_twisted_centraliser
-- name    : GlobalTheory.Tw.twisted_centraliser
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:57.45856+00:00
-- url     : https://prove2.me/theorems/3fbce241-79bf-50dc-9952-4c476d0b0053
-- title:
--   Tw: twisted centraliser
-- statement:
--   The Tw construction uses the twisted centraliser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L239-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L239-L248

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
open GlobalTheory.Tw.CentralizerAdjoin

theorem GlobalTheory.Tw.twisted_centraliser :
    ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R] [IsArtinianRing R] [IsReduced R] (δ : Matrix (Fin n) (Fin n) R),
      Reg δ → (∀ g h, adj δ (g * h) = adj δ h * adj δ g) ∧ (∀ (c : R) g h, adj δ (c • g + h) = star c • adj δ g + adj δ h) ∧
        adj δ (nrm δ) = (nrm δ)⁻¹ ∧
        (∀ g ∈ Algebra.adjoin R {nrm δ}, adj δ g ∈ Algebra.adjoin R {nrm δ} ∧ adj δ (adj δ g) = g) ∧
        (∀ g, g * nrm δ = nrm δ * g ↔ g ∈ Algebra.adjoin R {nrm δ}) ∧
        cent δ = {g | g ∈ Algebra.adjoin R {nrm δ} ∧ g * adj δ g = 1} := by sorry
