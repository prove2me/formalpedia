-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_exists_fields
-- name    : GlobalTheory.CompanionTheory.ProdExChart.exists_fields
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:58.190457+00:00
-- url     : https://prove2.me/theorems/9298a1fa-75eb-46df-abcb-177943b15234
-- title:
--   Prod Ex Chart: exists fields
-- statement:
--   The Prod Ex Chart construction uses the exists fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L197-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean#L197-L238

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

theorem GlobalTheory.CompanionTheory.ProdExChart.exists_fields {Hm : Mat n} (h : Hm * Hm = 1) : ∀ {d : ℕ} (X : Fin d → Mat n),
    (∀ j, Lie Hm (X j)) → ∃ Z : Fin d → (Fin d → ℝ) → Mat n, (∀ j t, Lie Hm (Z j t)) ∧
      (∀ j t (τ : ℝ), prodEx X (t + τ • (Pi.single j 1 : Fin d → ℝ)) = prodEx X t * ex (Z j t) τ) ∧
      (∀ j, ContDiff ℝ ∞ (Z j)) ∧ ∀ j, Z j 0 = X j
  := by sorry
