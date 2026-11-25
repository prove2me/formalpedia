-- Prove2me | Theorems.Thm_GlobalTheory_JR_HeightSquareIntegrable_height_sq_lintegral_lt_top
-- name    : GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:32:14.639325+00:00
-- url     : https://prove2.me/theorems/3b3da318-4fba-467a-87bf-cf19e6a562eb
-- title:
--   Height Square Integrable: height sq lintegral lt top
-- statement:
--   The Height Square Integrable construction uses the height sq lintegral lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L65-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L65-L312

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

theorem GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.K), μ.IsAddHaarMeasure → ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ < ⊤ := by sorry
