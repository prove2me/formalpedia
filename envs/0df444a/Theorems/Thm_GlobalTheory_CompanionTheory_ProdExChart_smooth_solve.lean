-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_smooth_solve
-- name    : GlobalTheory.CompanionTheory.ProdExChart.smooth_solve
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:43:17.571875+00:00
-- url     : https://prove2.me/theorems/aa29f88f-3974-5882-8d0a-e33b97f05405
-- title:
--   Prod Ex Chart: smooth solve
-- statement:
--   The Prod Ex Chart construction uses the smooth solve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L14-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L14-L61

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

theorem GlobalTheory.CompanionTheory.ProdExChart.smooth_solve {P F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℝ V) (M : P → F →L[ℝ] V) (hM : ContDiff ℝ ∞ M) (hL : ∀ t c, M t c ∈ L)
    (h0 : ∀ y ∈ L, ∃ c, M 0 c = y) :
    ∃ U : Set P, IsOpen U ∧ (0 : P) ∈ U ∧ ∀ y : P → V, ContDiff ℝ ∞ y → (∀ t, y t ∈ L) →
      ∃ c : P → F, ContDiffOn ℝ ∞ c U ∧ ∀ t ∈ U, M t (c t) = y t := by sorry
