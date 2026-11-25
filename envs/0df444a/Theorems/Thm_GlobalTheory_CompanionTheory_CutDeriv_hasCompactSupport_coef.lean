-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CutDeriv_hasCompactSupport_coef
-- name    : GlobalTheory.CompanionTheory.CutDeriv.hasCompactSupport_coef
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:04:29.757794+00:00
-- url     : https://prove2.me/theorems/9db6cf2a-1f7a-5576-abbc-1fba9f3e3659
-- title:
--   Cut Deriv: has Compact Support coef
-- statement:
--   The Cut Deriv construction uses the has Compact Support coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivation.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivation.lean#L40-L45

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CutDeriv
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem GlobalTheory.CompanionTheory.CutDeriv.hasCompactSupport_coef {ρ : Mat n → ℝ} (hc : HasCompactSupport ρ) {R : ℝ} (hR : 0 < R)
    (φ : PI.MtM n → ℂ) : HasCompactSupport fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * φ y := by sorry
