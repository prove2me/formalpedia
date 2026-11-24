-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_Idem_single_mul_single_of_ne
-- name    : GlobalTheory.JR.Et.Idem.single_mul_single_of_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:26:34.882378+00:00
-- url     : https://prove2.me/theorems/1609b15d-334b-4c6a-95c8-f2ba896598d1
-- title:
--   Idem: single mul single of ne
-- statement:
--   The Idem construction uses the single mul single of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdempotentDecompositionOfIntegrality.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdempotentDecompositionOfIntegrality.lean#L32-L38

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

theorem GlobalTheory.JR.Et.Idem.single_mul_single_of_ne {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroClass (R i)] {i j : ι}
    (h : i ≠ j) (a : R i) (b : R j) : (Pi.single i a : ∀ k, R k) * Pi.single j b = 0 := by sorry
