-- Prove2me | Theorems.Thm_GlobalTheory_T_fourierTransformKProd_locallyConstantCompactSupport
-- name    : GlobalTheory.T.fourierTransformKProd_locallyConstantCompactSupport
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:40:50.612812+00:00
-- url     : https://prove2.me/theorems/285a5f11-99c8-4446-8187-bdadaa354ab7
-- title:
--   T: fourier Transform KProd locally Constant Compact Support
-- statement:
--   The T construction uses the fourier Transform KProd locally Constant Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierTransformKProdLocallyConstantCompactSuppoStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierTransformKProdLocallyConstantCompactSuppoStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppo
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppoStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fourierTransformKProd_locallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by sorry
