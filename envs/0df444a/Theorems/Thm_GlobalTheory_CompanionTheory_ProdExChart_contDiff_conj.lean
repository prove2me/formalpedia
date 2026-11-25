-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_contDiff_conj
-- name    : GlobalTheory.CompanionTheory.ProdExChart.contDiff_conj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:26:31.456973+00:00
-- url     : https://prove2.me/theorems/b1ca1730-c4aa-5800-a8a0-84a2e0439c89
-- title:
--   Prod Ex Chart: cont Diff conj
-- statement:
--   The Prod Ex Chart construction uses the cont Diff conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L158-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L158-L165

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.ProdExChart.contDiff_conj {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {Hm : Mat n}
    (h : Hm * Hm = 1) {s : P → Mat n} (hs : ContDiff ℝ ∞ s) (hm : ∀ t, s t ∈ UH Hm) (Y : Mat n) :
    ContDiff ℝ ∞ (fun t => (s t)⁻¹ * Y * s t) := by sorry
