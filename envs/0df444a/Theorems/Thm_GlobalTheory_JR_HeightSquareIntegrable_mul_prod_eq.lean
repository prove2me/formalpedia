-- Prove2me | Theorems.Thm_GlobalTheory_JR_HeightSquareIntegrable_mul_prod_eq
-- name    : GlobalTheory.JR.HeightSquareIntegrable.mul_prod_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:32:27.047822+00:00
-- url     : https://prove2.me/theorems/93e08a1b-3205-456b-9f93-520482e47bd7
-- title:
--   Height Square Integrable: mul prod eq
-- statement:
--   The Height Square Integrable construction uses the mul prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L49-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L49-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HeightSquareIntegrable
variable {K : Type} [CommRing K] {m : ℕ} {f : Fin m → K}

theorem GlobalTheory.JR.HeightSquareIntegrable.mul_prod_eq (hid : ∀ i, f i * f i = f i) (hor : ∀ i j, i ≠ j → f i * f j = 0)
    (g : Fin m → K) (k : Fin m → ℕ) (j : Fin m) :
    f j * ∏ i, (f i * g i + (1 - f i)) ^ k i = f j * g j ^ k j := by sorry
