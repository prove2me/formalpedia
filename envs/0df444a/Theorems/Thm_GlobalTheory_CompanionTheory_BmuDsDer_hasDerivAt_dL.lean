-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDsDer_hasDerivAt_dL
-- name    : GlobalTheory.CompanionTheory.BmuDsDer.hasDerivAt_dL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:21:35.76424+00:00
-- url     : https://prove2.me/theorems/609b3d06-9760-44cd-bdbb-6ffac69a91cf
-- title:
--   Bmu Ds Der: has Deriv At d L
-- statement:
--   The Bmu Ds Der construction uses the has Deriv At d L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesDerivation.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesDerivation.lean#L78-L83

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

theorem GlobalTheory.CompanionTheory.BmuDsDer.hasDerivAt_dL {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) (Y g y : Mat n) :
    HasDerivAt (fun t => Φ (g * ex Y t, y)) (dL (fun g => g * Y) Φ (g, y)) 0 := by sorry
