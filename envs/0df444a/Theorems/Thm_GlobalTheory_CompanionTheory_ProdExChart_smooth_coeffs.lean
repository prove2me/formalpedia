-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_smooth_coeffs
-- name    : GlobalTheory.CompanionTheory.ProdExChart.smooth_coeffs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:22:23.65534+00:00
-- url     : https://prove2.me/theorems/0d11ee5e-5bd8-4674-9f0e-5a10616eecd5
-- title:
--   Prod Ex Chart: smooth coeffs
-- statement:
--   The Prod Ex Chart construction uses the smooth coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L63-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L63-L93

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdExChart

theorem GlobalTheory.CompanionTheory.ProdExChart.smooth_coeffs {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d e : ℕ}
    (L : Submodule ℝ V) (Z : Fin d → P → V) (Q : Fin e → V) (h3 : ∀ j, ContDiff ℝ ∞ (Z j))
    (h1 : ∀ j t, Z j t ∈ L) (hQ : ∀ i, Q i ∈ L)
    (h0 : ∀ y ∈ L, ∃ (a : Fin d → ℝ) (b : Fin e → ℝ), y = ∑ j, a j • Z j 0 + ∑ i, b i • Q i) :
    ∃ U : Set P, IsOpen U ∧ (0 : P) ∈ U ∧ ∀ y : P → V, ContDiff ℝ ∞ y → (∀ t, y t ∈ L) →
      ∃ (a : Fin d → P → ℝ) (b : Fin e → P → ℝ), (∀ j, ContDiffOn ℝ ∞ (a j) U) ∧
        (∀ i, ContDiffOn ℝ ∞ (b i) U) ∧ ∀ t ∈ U, y t = ∑ j, a j t • Z j t + ∑ i, b i t • Q i := by sorry
