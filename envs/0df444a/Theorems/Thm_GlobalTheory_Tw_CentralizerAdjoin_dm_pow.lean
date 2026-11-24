-- Prove2me | Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_dm_pow
-- name    : GlobalTheory.Tw.CentralizerAdjoin.dm_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:19.43495+00:00
-- url     : https://prove2.me/theorems/a47605eb-f9c7-4120-81c6-c4af6931736d
-- title:
--   Centralizer Adjoin: dm pow
-- statement:
--   The Centralizer Adjoin construction uses the dm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L42-L51

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

theorem GlobalTheory.Tw.CentralizerAdjoin.dm_pow (N g : Matrix (Fin n) (Fin n) R) (hc : g * N = N * g) (k : ℕ) :
    dm N g ^ (k + 1) = dm (N ^ (k + 1)) (((k + 1 : ℕ) : R) • (N ^ k * g)) := by sorry
