-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_adapted_dec_left
-- name    : GlobalTheory.CompanionTheory.BmuIwa.adapted_dec_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:20:44.198997+00:00
-- url     : https://prove2.me/theorems/11a1f9d8-897d-5bc2-855f-a1d55a8712cc
-- title:
--   Bmu Iwa: adapted dec left
-- statement:
--   The Bmu Iwa construction uses the adapted dec left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L82-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L82-L102

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

theorem GlobalTheory.CompanionTheory.BmuIwa.adapted_dec_left {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : xᴴ * dp p 0 c * x = dp p 0 c) :
    ∃ s κ : Matrix (Fin n) (Fin n) ℂ, sᴴ * dp p 0 c * s = dp p 0 c ∧ κᴴ * dp p 0 c * κ = dp p 0 c ∧
      s.BlockTriangular id ∧ κᴴ * κ = 1 ∧ x = s * κ := by sorry
