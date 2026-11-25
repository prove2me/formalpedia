-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_fix_inv
-- name    : GlobalTheory.CompanionTheory.BmuDecomp.fix_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:16.258143+00:00
-- url     : https://prove2.me/theorems/c078f6fd-b5fa-42be-b618-e09c68b3aedc
-- title:
--   Bmu Decomp: fix inv
-- statement:
--   The Bmu Decomp construction uses the fix inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L42-L45

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

theorem GlobalTheory.CompanionTheory.BmuDecomp.fix_inv {P Q : Matrix (Fin n) (Fin n) ℂ} (h : Q * P = 1) {v : Fin n → ℂ} (hv : P *ᵥ v = v) :
    Q *ᵥ v = v := by sorry
