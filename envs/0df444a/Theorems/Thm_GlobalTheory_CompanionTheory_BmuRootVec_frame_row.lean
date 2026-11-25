-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_frame_row
-- name    : GlobalTheory.CompanionTheory.BmuRootVec.frame_row
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:38.277817+00:00
-- url     : https://prove2.me/theorems/67e580e5-ab06-405a-84cd-f8c1056fc433
-- title:
--   Bmu Root Vec: frame row
-- statement:
--   The Bmu Root Vec construction uses the frame row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/RootVectors.lean#L161-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/RootVectors.lean#L161-L182

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuRootVec
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.BmuRootVec.frame_row {Γ : Mat (2 * r + k + 1)} (hΓ : Γᴴ * Hpk k r * Γ = Hq k r)
    {i i' : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (h : i.val + i'.val = 2 * r + k)
    (hf : Γ *ᵥ bvec i = bvec i) (l : Fin (2 * r + k + 1)) : Γ i' l = if l = i' then 1 else 0 := by sorry
