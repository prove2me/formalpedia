-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDsDer_contDiff_dW
-- name    : GlobalTheory.CompanionTheory.BmuDsDer.contDiff_dW
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:00:58.128635+00:00
-- url     : https://prove2.me/theorems/39d9c655-7b9e-4917-9502-a5b64306b9d8
-- title:
--   Bmu Ds Der: cont Diff d W
-- statement:
--   The Bmu Ds Der construction uses the cont Diff d W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesDerivation.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesDerivation.lean#L63-L67

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesDerivation
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuDsDer
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem GlobalTheory.CompanionTheory.BmuDsDer.contDiff_dW {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) : ∀ W, ContDiff ℝ ∞ (dW W Φ) := by sorry
