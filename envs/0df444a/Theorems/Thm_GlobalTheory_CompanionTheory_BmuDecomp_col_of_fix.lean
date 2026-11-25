-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_col_of_fix
-- name    : GlobalTheory.CompanionTheory.BmuDecomp.col_of_fix
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:08:31.696255+00:00
-- url     : https://prove2.me/theorems/8d2098a7-5d02-4cb7-b797-6ef6770e07e4
-- title:
--   Bmu Decomp: col of fix
-- statement:
--   The Bmu Decomp construction uses the col of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L55-L58

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
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.BmuDecomp.col_of_fix {P : Matrix (Fin n) (Fin n) ℂ} {i : Fin n} (h : P *ᵥ bvec i = bvec i) (j : Fin n) :
    P j i = if j = i then 1 else 0 := by sorry
