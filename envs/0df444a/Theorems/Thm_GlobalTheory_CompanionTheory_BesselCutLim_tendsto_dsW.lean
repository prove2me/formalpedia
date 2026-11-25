-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselCutLim_tendsto_dsW
-- name    : GlobalTheory.CompanionTheory.BesselCutLim.tendsto_dsW
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:22:21.794943+00:00
-- url     : https://prove2.me/theorems/1621bdc9-6d4a-57a9-aa83-d752c9bace61
-- title:
--   Bessel Cut Lim: tendsto ds W
-- statement:
--   The Bessel Cut Lim construction uses the tendsto ds W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivationLimit.lean#L60-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivationLimit.lean#L60-L94

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

theorem GlobalTheory.CompanionTheory.BesselCutLim.tendsto_dsW (hD : CutDer) (hσ : URep Hm σ) {μ : Measure (PI.MtM n)} (hμ : PI.IsHaarOnM (UH Hm) μ)
    {w : H} (hw : IsSm (UH Hm) σ w)
    (hi : ∀ v, IsSm (UH Hm) σ v → Integrable (fun y : PI.MtM n => ⟪v, σ (Matrix.of y) w⟫_ℂ) μ) {κ : ℂ}
    (hκ : ∀ v, IsSm (UH Hm) σ v →
      ∫ y : PI.MtM n, conj ⟪v, σ (Matrix.of y) w⟫_ℂ • σ (Matrix.of y) w ∂μ = κ • v)
    (W : List (Mat n)) : LieWd Hm W → ∀ ρ : Mat n → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      ∀ v, IsSm (UH Hm) σ v →
      Tendsto (fun N : ℕ => dsW σ W (cutI σ μ w ((N : ℝ) + 1) ρ v)) atTop (𝓝 ((ρ 0 : ℂ) • κ • dsW σ W v)) := by sorry
