-- Prove2me | Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_inv_mem_adjoin_of_isUnit
-- name    : GlobalTheory.Tw.CentralizerAdjoin.inv_mem_adjoin_of_isUnit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:38.757901+00:00
-- url     : https://prove2.me/theorems/9a0d1fcc-6415-4e39-956a-a0041aaf03b4
-- title:
--   Centralizer Adjoin: inv mem adjoin of is Unit
-- statement:
--   The Centralizer Adjoin construction uses the inv mem adjoin of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L105-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L105-L118

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

theorem GlobalTheory.Tw.CentralizerAdjoin.inv_mem_adjoin_of_isUnit {N : Matrix (Fin n) (Fin n) R} (hN : IsUnit N) :
    N⁻¹ ∈ Algebra.adjoin R {N} := by sorry
