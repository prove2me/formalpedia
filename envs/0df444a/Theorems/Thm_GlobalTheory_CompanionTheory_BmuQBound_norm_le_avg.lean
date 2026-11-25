-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuQBound_norm_le_avg
-- name    : GlobalTheory.CompanionTheory.BmuQBound.norm_le_avg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:02.35572+00:00
-- url     : https://prove2.me/theorems/f0112e2c-216a-483b-8e1a-7348f2f59c39
-- title:
--   Bmu QBound: norm le avg
-- statement:
--   The Bmu QBound construction uses the norm le avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/QuotientBoundOfFactorReduceChart.lean#L32-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/QuotientBoundOfFactorReduceChart.lean#L32-L58

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuotientBoundOfFactorReduceChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuQBound
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem GlobalTheory.CompanionTheory.BmuQBound.norm_le_avg {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) (h0 : ∀ t, 0 ≤ φ t)
    (h1 : ∫ t, φ t = 1) (f : (Fin d → ℝ) → V) (hf : Continuous f) (b : V)
    (hb : ∀ t, φ t ≠ 0 → ‖f t - b‖ ≤ ‖b‖ / 2) : ‖b‖ ≤ 2 * ‖∫ t, (φ t : ℂ) • f t‖ := by sorry
