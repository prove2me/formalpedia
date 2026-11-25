-- Prove2me | Theorems.Thm_GlobalTheory_exists_pow_eq_span_singleton_of_fg
-- name    : GlobalTheory.exists_pow_eq_span_singleton_of_fg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:25.172075+00:00
-- url     : https://prove2.me/theorems/2f06d0ba-9fb2-547a-8bac-7f18fb6ecd37
-- title:
--   Global Theory: exists pow eq span singleton of fg
-- statement:
--   The Global Theory construction uses the exists pow eq span singleton of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFiniteExtensionCapitulationComplex.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFiniteExtensionCapitulationComplex.lean#L7-L28

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

theorem GlobalTheory.exists_pow_eq_span_singleton_of_fg (E : Type) [Field E] [NumberField E]
    (I : Submodule (𝓞 E) E) (hI : I.FG) :
    ∃ n : ℕ, ∃ β : E, I ^ (n + 1) = Submodule.span (𝓞 E) {β} := by sorry
