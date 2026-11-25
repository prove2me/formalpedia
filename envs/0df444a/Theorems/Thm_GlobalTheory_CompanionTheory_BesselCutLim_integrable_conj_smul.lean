-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselCutLim_integrable_conj_smul
-- name    : GlobalTheory.CompanionTheory.BesselCutLim.integrable_conj_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:39:48.570837+00:00
-- url     : https://prove2.me/theorems/7d461c30-336f-59c9-b1d1-f3fcbc706e45
-- title:
--   Bessel Cut Lim: integrable conj smul
-- statement:
--   The Bessel Cut Lim construction uses the integrable conj smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivationLimit.lean#L39-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TruncatedDerivationLimit.lean#L39-L52

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

theorem GlobalTheory.CompanionTheory.BesselCutLim.integrable_conj_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (Mat n)}
    (hG : IsClosed G) {μ : Measure (PI.MtM n)} (hae : ∀ᵐ y ∂μ, (Matrix.of y : Mat n) ∈ G)
    {c : PI.MtM n → ℂ} (hc : Integrable c μ) {g : Mat n → E} (hg : ContinuousOn g G) {K : ℝ}
    (hK : ∀ x ∈ G, ‖g x‖ ≤ K) : Integrable (fun y => conj (c y) • g (Matrix.of y)) μ := by sorry
