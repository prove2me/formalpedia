-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_adapted_dec_one
-- name    : GlobalTheory.CompanionTheory.BmuIwa.adapted_dec_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:20:52.231468+00:00
-- url     : https://prove2.me/theorems/b0d98d95-9b04-5e0a-90bc-e8e979019eae
-- title:
--   Bmu Iwa: adapted dec one
-- statement:
--   The Bmu Iwa construction uses the adapted dec one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L14-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L14-L69

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwasawaDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuIwa
open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder

theorem GlobalTheory.CompanionTheory.BmuIwa.adapted_dec_one {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * dp p 0 c * g = dp p 0 c) :
    ∃ k B : Matrix (Fin n) (Fin n) ℂ, kᴴ * k = 1 ∧ kᴴ * dp p 0 c * k = dp p 0 c ∧
      Bᴴ * dp p 0 c * B = dp p 0 c ∧ g = k * B ∧ B.BlockTriangular id := by sorry
