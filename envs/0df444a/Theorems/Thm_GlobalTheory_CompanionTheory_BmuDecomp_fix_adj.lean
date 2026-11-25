-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_fix_adj
-- name    : GlobalTheory.CompanionTheory.BmuDecomp.fix_adj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:19:32.002206+00:00
-- url     : https://prove2.me/theorems/86d82db7-62f0-54ce-a5f6-236902f7ad73
-- title:
--   Bmu Decomp: fix adj
-- statement:
--   The Bmu Decomp construction uses the fix adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L51-L53

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

theorem GlobalTheory.CompanionTheory.BmuDecomp.fix_adj {A B P : Matrix (Fin n) (Fin n) ℂ} (hP : Pᴴ * A * P = B) {v w : Fin n → ℂ} (hv : P *ᵥ v = v)
    (hA : A *ᵥ v = w) (hB : B *ᵥ v = w) : Pᴴ *ᵥ w = w := by sorry
