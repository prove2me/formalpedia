-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CutDeriv_notMem_tsupport
-- name    : GlobalTheory.CompanionTheory.CutDeriv.notMem_tsupport
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:04:24.899546+00:00
-- url     : https://prove2.me/theorems/7b0a6ea4-22b5-5743-a4e7-cfcf752b13e0
-- title:
--   Cut Deriv: not Mem tsupport
-- statement:
--   The Cut Deriv construction uses the not Mem tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivation.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivation.lean#L23-L31

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

theorem GlobalTheory.CompanionTheory.CutDeriv.notMem_tsupport {ρ : Mat n → ℝ} {R : ℝ} (hR : 0 < R) (X : Mat n) {T : Set ℝ} {t : ℝ} (ht : t ∈ T)
    {y : PI.MtM n}
    (hy : y ∉ (fun p : ℝ × Mat n => (Matrix.of.symm (R • (ex X p.1 * p.2)) : PI.MtM n)) '' (T ×ˢ tsupport ρ)) :
    ex X (-t) * (R⁻¹ • Matrix.of y) ∉ tsupport ρ := by sorry
