-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_measure_doubleCoset_diagPow
-- name    : GroundTheory.Automorphic.Measures.measure_doubleCoset_diagPow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:43.87131+00:00
-- url     : https://prove2.me/theorems/58c8fc8b-60fc-5a3f-b14a-2508933e3e63
-- title:
--   Measures: measure double Coset diag Pow
-- statement:
--   The Measures construction uses the measure double Coset diag Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L179-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L179-L185

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

theorem GroundTheory.Automorphic.Measures.measure_doubleCoset_diagPow [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsMulLeftInvariant] (a : Fin n → ℤ) :
    μ (doubleCoset (Cartan.diagPow F n a) (GLnLocal.integralGL F n : Set (GL (Fin n) F))
        (GLnLocal.integralGL F n)) =
      (((GLnLocal.integralGL F n).map (MulAut.conj (Cartan.diagPow F n a)).toMonoidHom).relIndex
        (GLnLocal.integralGL F n) : ℝ≥0∞) * μ (GLnLocal.integralGL F n) := by sorry
