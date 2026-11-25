-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_conj_mul
-- name    : GlobalTheory.CompanionTheory.BmuIwa.conj_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:43:10.066808+00:00
-- url     : https://prove2.me/theorems/c042a278-441b-4c4b-aca6-42ebb4c9bbea
-- title:
--   Bmu Iwa: conj mul
-- statement:
--   The Bmu Iwa construction uses the conj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L77-L80

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

theorem GlobalTheory.CompanionTheory.BmuIwa.conj_mul {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A) * g = 1 := by sorry
