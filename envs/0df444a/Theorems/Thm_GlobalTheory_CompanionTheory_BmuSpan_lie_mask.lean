-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_lie_mask
-- name    : GlobalTheory.CompanionTheory.BmuSpan.lie_mask
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:24.527047+00:00
-- url     : https://prove2.me/theorems/56c5ca3a-5262-4d2b-806f-5747a163ed74
-- title:
--   Bmu Span: lie mask
-- statement:
--   The Bmu Span construction uses the lie mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L95-L102

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

theorem GlobalTheory.CompanionTheory.BmuSpan.lie_mask {p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Prop}
    (hp : ∀ i j, p (pr k r j) i → p (pr k r i) j) {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Lie (Hq k r) X) : Lie (Hq k r) (mask p X) := by sorry
