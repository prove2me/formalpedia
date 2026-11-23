-- Prove2me | Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_semi
-- name    : GlobalTheory.Tw.CentralizerAdjoin.adj_semi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:25.616972+00:00
-- url     : https://prove2.me/theorems/3e75866c-6f17-4c83-b1d9-d694ba902175
-- title:
--   Centralizer Adjoin: adj semi
-- statement:
--   The Centralizer Adjoin construction uses the adj semi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L127-L130

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

theorem GlobalTheory.Tw.CentralizerAdjoin.adj_semi (δ : Matrix (Fin n) (Fin n) R) (c : R) (g h : Matrix (Fin n) (Fin n) R) :
    adj δ (c • g + h) = star c • adj δ g + adj δ h := by sorry
