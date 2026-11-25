-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_conj_mem
-- name    : GlobalTheory.CompanionTheory.BmuIwa.conj_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:20.337094+00:00
-- url     : https://prove2.me/theorems/b4266c01-f9b0-50d6-b77c-723ef6bb1d3a
-- title:
--   Bmu Iwa: conj mem
-- statement:
--   The Bmu Iwa construction uses the conj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L71-L75

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

theorem GlobalTheory.CompanionTheory.BmuIwa.conj_mem {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1) (hAH : Aᴴ = A)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A)ᴴ * A * (A * gᴴ * A) = A := by sorry
