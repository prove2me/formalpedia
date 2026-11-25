-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuWordBd_exists_basis_sub
-- name    : GlobalTheory.CompanionTheory.BmuWordBd.exists_basis_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:22:24.605064+00:00
-- url     : https://prove2.me/theorems/baf3a6b0-6238-41cb-862b-72f9d11c7984
-- title:
--   Bmu Word Bd: exists basis sub
-- statement:
--   The Bmu Word Bd construction uses the exists basis sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordLengthBoundOfLinear.lean#L27-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordLengthBoundOfLinear.lean#L27-L45

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordLengthBoundOfLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuWordBd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem GlobalTheory.CompanionTheory.BmuWordBd.exists_basis_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Submodule ℝ E) :
    ∃ (N : ℕ) (b : Fin N → E) (κ : ℝ), 0 ≤ κ ∧ (∀ i, b i ∈ S) ∧
      ∀ X, X ∈ S → ∃ c : Fin N → ℝ, X = ∑ i, c i • b i ∧ ∀ i, |c i| ≤ κ * ‖X‖ := by sorry
