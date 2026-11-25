-- Prove2me | Theorems.Thm_GlobalTheory_T_primitiveTuplesWithGramMatrix_hensel_count
-- name    : GlobalTheory.T.primitiveTuplesWithGramMatrix_hensel_count
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:45:20.166061+00:00
-- url     : https://prove2.me/theorems/3a7f7b64-1cc4-56b8-aca6-d5a9c6d13842
-- title:
--   T: primitive Tuples With Gram Matrix hensel count
-- statement:
--   The T construction uses the primitive Tuples With Gram Matrix hensel count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesWithGramMatrixHenselCountStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesWithGramMatrixHenselCountStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCountStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.primitiveTuplesWithGramMatrix_hensel_count : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → IsNilpotent p → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), (∀ a b, c (G b a) = G a b) → Set.ncard (sols c n G) * Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} = Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by sorry
