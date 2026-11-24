-- Prove2me | Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_nrm
-- name    : GlobalTheory.Tw.CentralizerAdjoin.adj_nrm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:27.173966+00:00
-- url     : https://prove2.me/theorems/416221d9-f687-4074-8d50-f78384484bf0
-- title:
--   Centralizer Adjoin: adj nrm
-- statement:
--   The Centralizer Adjoin construction uses the adj nrm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L151-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L151-L157

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

theorem GlobalTheory.Tw.CentralizerAdjoin.adj_nrm {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : adj δ (nrm δ) = (nrm δ)⁻¹ := by sorry
