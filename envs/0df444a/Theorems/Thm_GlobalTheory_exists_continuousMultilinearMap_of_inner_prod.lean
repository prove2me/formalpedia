-- Prove2me | Theorems.Thm_GlobalTheory_exists_continuousMultilinearMap_of_inner_prod
-- name    : GlobalTheory.exists_continuousMultilinearMap_of_inner_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:22.616497+00:00
-- url     : https://prove2.me/theorems/46285643-c27e-4719-80e1-5dd8737366c8
-- title:
--   Global Theory: exists continuous Multilinear Map of inner prod
-- statement:
--   The Global Theory construction uses the exists continuous Multilinear Map of inner prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsContinuousMultilinearMapOfInnerProd.lean#L23-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsContinuousMultilinearMapOfInnerProd.lean#L23-L60

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

theorem GlobalTheory.exists_continuousMultilinearMap_of_inner_prod {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (t : (∀ v, H v) → E)
    (hin : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range t) : Set E)) :
    ∃ m : ContinuousMultilinearMap ℂ H E, (∀ x, m x = t x) ∧ ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by sorry
