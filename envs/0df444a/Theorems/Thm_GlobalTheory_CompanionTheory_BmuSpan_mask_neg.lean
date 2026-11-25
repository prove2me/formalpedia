-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_mask_neg
-- name    : GlobalTheory.CompanionTheory.BmuSpan.mask_neg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:57.453932+00:00
-- url     : https://prove2.me/theorems/c5c1210d-8602-5841-856a-86e8363eb2e4
-- title:
--   Bmu Span: mask neg
-- statement:
--   The Bmu Span construction uses the mask neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L92-L93

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

theorem GlobalTheory.CompanionTheory.BmuSpan.mask_neg {n : ℕ} {p : Fin n → Fin n → Prop} {X : Matrix (Fin n) (Fin n) ℂ} {i j : Fin n} (h : ¬ p i j) :
    mask p X i j = 0 := by sorry
