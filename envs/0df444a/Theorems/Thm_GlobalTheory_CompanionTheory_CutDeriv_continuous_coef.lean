-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CutDeriv_continuous_coef
-- name    : GlobalTheory.CompanionTheory.CutDeriv.continuous_coef
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:05:08.52198+00:00
-- url     : https://prove2.me/theorems/a25fabf9-f4c2-51bc-b0a1-df58f007a6f4
-- title:
--   Cut Deriv: continuous coef
-- statement:
--   The Cut Deriv construction uses the continuous coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivation.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivation.lean#L47-L50

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

theorem GlobalTheory.CompanionTheory.CutDeriv.continuous_coef {ρ : Mat n → ℝ} (hρ : Continuous ρ) (R : ℝ) {F : Mat n → H} (hF : Continuous F) (v : H) :
    Continuous fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ := by sorry
