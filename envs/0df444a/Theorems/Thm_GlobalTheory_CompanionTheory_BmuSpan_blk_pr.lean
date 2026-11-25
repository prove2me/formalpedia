-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_blk_pr
-- name    : GlobalTheory.CompanionTheory.BmuSpan.blk_pr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:35.877273+00:00
-- url     : https://prove2.me/theorems/9b12b024-3125-4f09-9142-8515acb04729
-- title:
--   Bmu Span: blk pr
-- statement:
--   The Bmu Span construction uses the blk pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L124-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L124-L128

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SpanGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu GlobalTheory.CompanionTheory.BmuDecomp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuSpan
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.BmuSpan.blk_pr (i j : Fin (2 * r + k + 1)) : blk k r (pr k r j) i ↔ blk k r (pr k r i) j := by sorry
