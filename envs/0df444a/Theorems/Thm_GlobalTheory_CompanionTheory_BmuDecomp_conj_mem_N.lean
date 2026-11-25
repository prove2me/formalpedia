-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_conj_mem_N
-- name    : GlobalTheory.CompanionTheory.BmuDecomp.conj_mem_N
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:21:12.087806+00:00
-- url     : https://prove2.me/theorems/8fb337f5-a0b6-4342-9e6f-c29160487338
-- title:
--   Bmu Decomp: conj mem N
-- statement:
--   The Bmu Decomp construction uses the conj mem N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L134-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L134-L170

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_conj_mem_N

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuDecomp
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.BmuDecomp.conj_mem_N {P Q m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Pᴴ * Hpk k r * P = Hq k r) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hf : ∀ a : Fin r, P *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ P *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hm : m ∈ Nq k r) : P * m * Q ∈ Nset k r := by sorry
