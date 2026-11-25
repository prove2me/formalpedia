-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ncard_dependent_le
-- name    : GlobalTheory.GramCount.ncard_dependent_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:00.932136+00:00
-- url     : https://prove2.me/theorems/3394f5b7-1621-4e7b-920d-0296fc48b18b
-- title:
--   Gram Count: ncard dependent le
-- statement:
--   The Gram Count construction uses the ncard dependent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardDependentVectorsAffineGramLe.lean#L140-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardDependentVectorsAffineGramLe.lean#L140-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
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

theorem GlobalTheory.GramCount.ncard_dependent_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) →
    ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k ≤ n →
    ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B),
    Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
      ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ≤ 2 * q ^ n := by sorry
