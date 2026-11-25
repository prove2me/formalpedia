-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ncard_sols_residue
-- name    : GlobalTheory.GramCount.ncard_sols_residue
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:01.210843+00:00
-- url     : https://prove2.me/theorems/9499ba4d-c5ba-48fc-bb44-af46b9efbe6a
-- title:
--   Gram Count: ncard sols residue
-- statement:
--   The Gram Count construction uses the ncard sols residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesWithGramMatrixResidueRing.lean#L139-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesWithGramMatrixResidueRing.lean#L139-L145

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
variable {B : Type} [CommRing B]

theorem GlobalTheory.GramCount.ncard_sols_residue : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (m n : ℕ), 2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) → (q : ℝ) ^ (2 * n * m - m ^ 2) ≤ 2 * (Set.ncard (sols c n G) : ℝ) ∧ (Set.ncard (sols c n G) : ℝ) ≤ 2 * (q : ℝ) ^ (2 * n * m - m ^ 2) := by sorry
