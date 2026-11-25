-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_block_of_fix
-- name    : GlobalTheory.CompanionTheory.BmuDecomp.block_of_fix
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:29:06.614882+00:00
-- url     : https://prove2.me/theorems/dbc9ba11-ca15-536b-87d1-3df19504c9b3
-- title:
--   Bmu Decomp: block of fix
-- statement:
--   The Bmu Decomp construction uses the block of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L119-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L119-L132

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
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

theorem GlobalTheory.CompanionTheory.BmuDecomp.block_of_fix {A B P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : Pᴴ * A * P = B)
    (hA : ∀ a : Fin r, A *ᵥ bvec (eI k r a) = bvec (esI k r a) ∧ A *ᵥ bvec (esI k r a) = bvec (eI k r a))
    (hB : ∀ a : Fin r, B *ᵥ bvec (eI k r a) = bvec (esI k r a) ∧ B *ᵥ bvec (esI k r a) = bvec (eI k r a))
    (hf : ∀ a : Fin r, P *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ P *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    P j i = (if j = i then 1 else 0) ∧ P i j = (if j = i then 1 else 0) := by sorry
