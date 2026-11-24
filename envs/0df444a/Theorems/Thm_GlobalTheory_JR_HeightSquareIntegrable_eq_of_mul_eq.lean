-- Prove2me | Theorems.Thm_GlobalTheory_JR_HeightSquareIntegrable_eq_of_mul_eq
-- name    : GlobalTheory.JR.HeightSquareIntegrable.eq_of_mul_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:46:29.702661+00:00
-- url     : https://prove2.me/theorems/285c0c2f-938e-46e1-8e93-b294a2f35ae9
-- title:
--   Height Square Integrable: eq of mul eq
-- statement:
--   The Height Square Integrable construction uses the eq of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L29-L32

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

theorem GlobalTheory.JR.HeightSquareIntegrable.eq_of_mul_eq (hsum : ∑ i, f i = 1) {x y : K} (h : ∀ j, f j * x = f j * y) : x = y := by sorry
