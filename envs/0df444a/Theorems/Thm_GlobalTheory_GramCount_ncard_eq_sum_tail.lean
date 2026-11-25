-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ncard_eq_sum_tail
-- name    : GlobalTheory.GramCount.ncard_eq_sum_tail
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:29:26.244247+00:00
-- url     : https://prove2.me/theorems/e38472a6-e730-4cf6-b6a3-1c1d2bee9823
-- title:
--   Gram Count: ncard eq sum tail
-- statement:
--   The Gram Count construction uses the ncard eq sum tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesWithGramMatrixResidueRing.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesWithGramMatrixResidueRing.lean#L10-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTupleExtensionsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesWithGramMatrixResidueRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount

theorem GlobalTheory.GramCount.ncard_eq_sum_tail {α : Type} [Fintype α] {m : ℕ} (S : Set (Fin (m + 1) → α))
    (T : Set (Fin m → α)) (h : ∀ X ∈ S, Fin.tail X ∈ T) :
    S.ncard = ∑ x ∈ T.toFinset, Set.ncard {y : α | (Fin.cons y x : Fin (m + 1) → α) ∈ S} := by sorry
