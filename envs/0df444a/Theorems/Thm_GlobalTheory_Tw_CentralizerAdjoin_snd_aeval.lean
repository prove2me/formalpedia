-- Prove2me | Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_snd_aeval
-- name    : GlobalTheory.Tw.CentralizerAdjoin.snd_aeval
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:26.685307+00:00
-- url     : https://prove2.me/theorems/de393e99-f483-4dd6-be07-5aacd52fe949
-- title:
--   Centralizer Adjoin: snd aeval
-- statement:
--   The Centralizer Adjoin construction uses the snd aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L59-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L59-L81

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

theorem GlobalTheory.Tw.CentralizerAdjoin.snd_aeval (N g : Matrix (Fin n) (Fin n) R) (hc : g * N = N * g) (P : (DualNumber R)[X]) :
    ∃ Q : R[X], (aeval (dm N g) P).map TrivSqZeroExt.snd =
      aeval N (derivative (P.map (TrivSqZeroExt.fstHom R R R).toRingHom)) * g + aeval N Q := by sorry
