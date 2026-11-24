-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_Idem_single_one_mul
-- name    : GlobalTheory.JR.Et.Idem.single_one_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:26:28.48969+00:00
-- url     : https://prove2.me/theorems/de2271e3-4f0c-40c3-993a-8234a347ef7a
-- title:
--   Idem: single one mul
-- statement:
--   The Idem construction uses the single one mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdempotentDecompositionOfIntegrality.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdempotentDecompositionOfIntegrality.lean#L40-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegrality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et GlobalTheory.JR.Et.Idem

theorem GlobalTheory.JR.Et.Idem.single_one_mul {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroOneClass (R i)] (i : ι)
    (x : ∀ j, R j) : (Pi.single i 1 : ∀ j, R j) * x = Pi.single i (x i) := by sorry
