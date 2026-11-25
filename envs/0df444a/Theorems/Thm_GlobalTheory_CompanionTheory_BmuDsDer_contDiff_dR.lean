-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDsDer_contDiff_dR
-- name    : GlobalTheory.CompanionTheory.BmuDsDer.contDiff_dR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:20:19.736256+00:00
-- url     : https://prove2.me/theorems/6c0787dc-6dd3-5965-9fa2-0fe67368e367
-- title:
--   Bmu Ds Der: cont Diff d R
-- statement:
--   The Bmu Ds Der construction uses the cont Diff d R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesDerivation.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesDerivation.lean#L27-L29

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
variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.CompanionTheory.BmuDsDer.contDiff_dR {b : E' → E'} (hb : ContDiff ℝ ∞ b) {Φ : E × E' → V} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (dR b Φ) := by sorry
