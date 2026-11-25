-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_PtAlg_ptEntryL_append
-- name    : GlobalTheory.SgLoc.PtAlg.ptEntryL_append
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:18.643074+00:00
-- url     : https://prove2.me/theorems/29e2c222-8beb-4eea-9242-f8d551fba726
-- title:
--   Pt Alg: pt Entry L append
-- statement:
--   The Pt Alg construction uses the pt Entry L append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SameBlockAppend.lean#L11-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SameBlockAppend.lean#L11-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.PtAlg
variable {E : Type} [CommRing E]

theorem GlobalTheory.SgLoc.PtAlg.ptEntryL_append (bs : List (Eˣ × ℕ+)) (t : Eˣ) (s : ℕ+) :
    ∀ (m : ℕ), (bs.map (fun b => (b.2 : ℕ))).sum = m → ∀ a b : ℕ,
      ptEntryL (bs ++ [(t, s)]) a b =
        if a < m ∧ b < m then ptEntryL bs a b
        else if m ≤ a ∧ m ≤ b ∧ a + b + 1 = 2 * m + s then (t : E) else 0 := by sorry
