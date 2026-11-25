-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_prodEx_succ
-- name    : GlobalTheory.CompanionTheory.ProdExChart.prodEx_succ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:26:24.039182+00:00
-- url     : https://prove2.me/theorems/b838fe21-6671-5802-8737-c261bf95d18f
-- title:
--   Prod Ex Chart: prod Ex succ
-- statement:
--   The Prod Ex Chart construction uses the prod Ex succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L167-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L167-L169

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

theorem GlobalTheory.CompanionTheory.ProdExChart.prodEx_succ {d : ℕ} (X : Fin (d + 1) → Mat n) (t : Fin (d + 1) → ℝ) :
    prodEx X t = ex (X 0) (t 0) * prodEx (fun j => X j.succ) (fun j => t j.succ) := by sorry
