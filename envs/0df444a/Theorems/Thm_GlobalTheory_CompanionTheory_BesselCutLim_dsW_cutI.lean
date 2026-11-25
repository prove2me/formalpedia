-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselCutLim_dsW_cutI
-- name    : GlobalTheory.CompanionTheory.BesselCutLim.dsW_cutI
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:22:47.415733+00:00
-- url     : https://prove2.me/theorems/b1bf24a8-fb30-5595-8555-ecb6ecabbfcc
-- title:
--   Bessel Cut Lim: ds W cut I
-- statement:
--   The Bessel Cut Lim construction uses the ds W cut I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivationLimit.lean#L96-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivationLimit.lean#L96-L126

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivationLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCutLim
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Hm : Mat n}
  {σ : Mat n → (H →L[ℂ] H)}

theorem GlobalTheory.CompanionTheory.BesselCutLim.dsW_cutI (hσ : URep Hm σ) {μ : Measure (PI.MtM n)} (hμ : PI.IsHaarOnM (UH Hm) μ)
    {w : H} (hw : IsSm (UH Hm) σ w) {R : ℝ} (hR : 0 < R) {ρ : Mat n → ℝ} (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (v : H) {W : List (Mat n)} (hW : LieWd Hm W) :
    Integrable (fun y : PI.MtM n => ((ρ (R⁻¹ • Matrix.of y) : ℂ) * conj ⟪v, σ (Matrix.of y) w⟫_ℂ) •
      dsW σ W (σ (Matrix.of y) w)) μ ∧
    dsW σ W (cutI σ μ w R ρ v) = ∫ y : PI.MtM n, ((ρ (R⁻¹ • Matrix.of y) : ℂ) * conj ⟪v, σ (Matrix.of y) w⟫_ℂ) •
      dsW σ W (σ (Matrix.of y) w) ∂μ := by sorry
