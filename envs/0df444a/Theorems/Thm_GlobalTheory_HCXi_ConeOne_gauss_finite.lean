-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeOne_gauss_finite
-- name    : GlobalTheory.HCXi.ConeOne.gauss_finite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:52:02.570599+00:00
-- url     : https://prove2.me/theorems/18e26061-eade-5b8a-9392-bbb89caa4a8a
-- title:
--   Cone One: gauss finite
-- statement:
--   The Cone One construction uses the gauss finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasurePosRank.lean#L169-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasurePosRank.lean#L169-L208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeOne
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8

theorem GlobalTheory.HCXi.ConeOne.gauss_finite {X : Type*} [MeasurableSpace X] (m : Measure X) (q : X → ℝ) (hq : Measurable q) (h0 : ∀ v, 0 ≤ q v)
    (d : ℕ) (hh : ∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ v, f (s * q v) ∂m) = ENNReal.ofReal (s ^ (-(d : ℝ))) * ∫⁻ v, f (q v) ∂m)
    (hfin : m {v | q v ≤ 1} < ∞) : (∫⁻ v, ENNReal.ofReal (Real.exp (-q v)) ∂m) ≠ ∞ := by sorry
