-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDsAd_lie_conj
-- name    : GlobalTheory.CompanionTheory.BmuDsAd.lie_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:25.778147+00:00
-- url     : https://prove2.me/theorems/332f220d-25b8-5d25-88df-0ad28eccd5fa
-- title:
--   Bmu Ds Ad: lie conj
-- statement:
--   The Bmu Ds Ad construction uses the lie conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesAdjoint.lean#L24-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesAdjoint.lean#L24-L41

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuDsAd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.BmuDsAd.lie_conj {Hm y X : Mat n} (hy : IsUnit y) (hyH : yᴴ * Hm * y = Hm) (hX : Lie Hm X) :
    Lie Hm (y⁻¹ * X * y) := by sorry
