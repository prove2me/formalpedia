-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_span_hq
-- name    : GlobalTheory.CompanionTheory.BmuSpan.span_hq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:37:31.762698+00:00
-- url     : https://prove2.me/theorems/c80b7029-7389-51d2-8115-7ca2032f349b
-- title:
--   Bmu Span: span hq
-- statement:
--   The Bmu Span construction uses the span hq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L130-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L130-L185

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

theorem GlobalTheory.CompanionTheory.BmuSpan.span_hq (hk : 1 ≤ k) {Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hY : Lie (Hq k r) Y) :
    ∃ B A C : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Lie (Hq k r) B ∧ Lie (Hq k r) A ∧ Lie (Hq k r) C ∧ (∀ i j, ¬ blk k r i j → B i j = 0) ∧
      (∀ i, B i (wI k r 0) = B i (wI k r (Fin.last k))) ∧
      (∀ i j, ¬ (up k r i j ∧ ¬ blk k r i j) → A i j = 0) ∧ (∀ i j, up k r i j → C i j = 0) ∧ Y = B + A + C := by sorry
