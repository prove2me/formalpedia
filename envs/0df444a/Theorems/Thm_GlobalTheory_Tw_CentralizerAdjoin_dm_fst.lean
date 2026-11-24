-- Prove2me | Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_dm_fst
-- name    : GlobalTheory.Tw.CentralizerAdjoin.dm_fst
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:06.111802+00:00
-- url     : https://prove2.me/theorems/07f1731a-736b-4e15-ac10-1e8a00a035e4
-- title:
--   Centralizer Adjoin: dm fst
-- statement:
--   The Centralizer Adjoin construction uses the dm fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L18-L19

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

theorem GlobalTheory.Tw.CentralizerAdjoin.dm_fst (U V : Matrix (Fin n) (Fin n) R) : (dm U V).map TrivSqZeroExt.fst = U := by sorry
