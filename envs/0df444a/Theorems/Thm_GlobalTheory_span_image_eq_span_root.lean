-- Prove2me | Theorems.Thm_GlobalTheory_span_image_eq_span_root
-- name    : GlobalTheory.span_image_eq_span_root
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:33.656511+00:00
-- url     : https://prove2.me/theorems/dc00eb2d-22ae-4bd8-b998-bbf818d81d29
-- title:
--   Global Theory: span image eq span root
-- statement:
--   The Global Theory construction uses the span image eq span root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFiniteExtensionCapitulationComplex.lean#L30-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFiniteExtensionCapitulationComplex.lean#L30-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFiniteExtensionCapitulationComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.span_image_eq_span_root {E M : Type} [Field E] [Field M] (ψ : E →+* M)
    (I : Submodule (𝓞 E) E) (n : ℕ) (β : E) (hβ : I ^ (n + 1) = Submodule.span (𝓞 E) {β})
    (γ : M) (hγ : γ ^ (n + 1) = ψ β) :
    Submodule.span (𝓞 M) (ψ '' I) = Submodule.span (𝓞 M) {γ} := by sorry
