-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_inner_eq_on_dense_span
-- name    : GlobalTheory.eq_of_inner_eq_on_dense_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:41:04.55497+00:00
-- url     : https://prove2.me/theorems/29b4a3ae-5e7b-4354-905f-e9614c3da97f
-- title:
--   Global Theory: eq of inner eq on dense span
-- statement:
--   The Global Theory construction uses the eq of inner eq on dense span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsContinuousMultilinearMapOfInnerProd.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsContinuousMultilinearMapOfInnerProd.lean#L9-L21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsContinuousMultilinearMapOfInnerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.eq_of_inner_eq_on_dense_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} (hs : Dense (Submodule.span ℂ s : Set E)) {a b : E}
    (h : ∀ y ∈ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ) : a = b := by sorry
