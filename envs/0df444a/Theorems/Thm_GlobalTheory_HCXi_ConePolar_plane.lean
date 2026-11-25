-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConePolar_plane
-- name    : GlobalTheory.HCXi.ConePolar.plane
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:51:13.41031+00:00
-- url     : https://prove2.me/theorems/5a42720a-8c5c-432d-8602-53bbf533280d
-- title:
--   Cone Polar: plane
-- statement:
--   The Cone Polar construction uses the plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralHyperboloidFibration.lean#L53-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralHyperboloidFibration.lean#L53-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConePolar

theorem GlobalTheory.HCXi.ConePolar.plane (a : ℝ) (ha : 0 ≤ a) (F : ℝ → ℝ≥0∞) (g : ℂ → ℝ≥0∞) (hF : Measurable F) (hg : Measurable g) :
    ∫⁻ z : ℂ, Set.indicator {z : ℂ | a < Complex.normSq z} (fun z => F (Complex.normSq z - a) * g z) z
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((Real.sqrt (a + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ))) := by sorry
