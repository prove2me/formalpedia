-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_dg_mem
-- name    : GlobalTheory.CompanionTheory.BmuDecomp.dg_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:19:45.094799+00:00
-- url     : https://prove2.me/theorems/036a65c7-c4a1-5171-a062-ba0cc91bb938
-- title:
--   Bmu Decomp: dg mem
-- statement:
--   The Bmu Decomp construction uses the dg mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L172-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfIwasawaLeviCartan.lean#L172-L182

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

theorem GlobalTheory.CompanionTheory.BmuDecomp.dg_mem {d : Fin (2 * r + k + 1) → ℝ} (hd : IsTor k r d) : dg d ∈ UH (Hq k r) := by sorry
