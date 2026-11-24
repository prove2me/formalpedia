-- Prove2me | Theorems.Thm_GlobalTheory_JR_HeightSquareIntegrable_mul_eq_iff_mk
-- name    : GlobalTheory.JR.HeightSquareIntegrable.mul_eq_iff_mk
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:32:27.290799+00:00
-- url     : https://prove2.me/theorems/1cbd2cf6-1b2d-435a-adb6-1ebefcf340e2
-- title:
--   Height Square Integrable: mul eq iff mk
-- statement:
--   The Height Square Integrable construction uses the mul eq iff mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L41-L47

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

theorem GlobalTheory.JR.HeightSquareIntegrable.mul_eq_iff_mk (hid : ∀ i, f i * f i = f i) (j : Fin m) (x y : K) :
    f j * x = f j * y ↔
      Ideal.Quotient.mk (Ideal.span {1 - f j}) x = Ideal.Quotient.mk (Ideal.span {1 - f j}) y := by sorry
