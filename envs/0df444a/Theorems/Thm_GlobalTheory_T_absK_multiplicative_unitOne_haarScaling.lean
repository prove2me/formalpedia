-- Prove2me | Theorems.Thm_GlobalTheory_T_absK_multiplicative_unitOne_haarScaling
-- name    : GlobalTheory.T.absK_multiplicative_unitOne_haarScaling
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:40.134671+00:00
-- url     : https://prove2.me/theorems/9b719cea-4618-40f1-96f7-3ef2105035e3
-- title:
--   T: abs K multiplicative unit One haar Scaling
-- statement:
--   The T construction uses the abs K multiplicative unit One haar Scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMultiplicativeUnitOneHaarScalingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMultiplicativeUnitOneHaarScalingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScaling
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScalingStatement
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

theorem GlobalTheory.T.absK_multiplicative_unitOne_haarScaling : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) := by sorry
