-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CutDeriv_apply_cutI
-- name    : GlobalTheory.CompanionTheory.CutDeriv.apply_cutI
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:22:08.993684+00:00
-- url     : https://prove2.me/theorems/dba324ed-91ea-48c1-839b-e7225aee9bef
-- title:
--   Cut Deriv: apply cut I
-- statement:
--   The Cut Deriv construction uses the apply cut I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivation.lean#L67-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivation.lean#L67-L95

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
variable {Hm : Mat n} {σ : Mat n → (H →L[ℂ] H)} {μ : Measure (PI.MtM n)} {w : H} {F : Mat n → H}
variable [CompleteSpace H]

theorem GlobalTheory.CompanionTheory.CutDeriv.apply_cutI (h : URep Hm σ) (hμ : PI.IsHaarOnM (UH Hm) μ) (hF : Continuous F)
    (hFw : ∀ a ∈ UH Hm, F a = σ a w) {R : ℝ} (hR : 0 < R) {ρ : Mat n → ℝ} (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (v : H) {X : Mat n} (hX : ∀ t, ex X t ∈ UH Hm) (t : ℝ) :
    σ (ex X t) (cutI σ μ w R ρ v) =
      ∫ y : PI.MtM n, ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) •
        F (Matrix.of y) ∂μ := by sorry
