-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ncard_sols_eta
-- name    : GlobalTheory.GramCount.ncard_sols_eta
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:27:46.217801+00:00
-- url     : https://prove2.me/theorems/30c1e699-a446-5927-8f2e-dadd7acde49e
-- title:
--   Gram Count: ncard sols eta
-- statement:
--   The Gram Count construction uses the ncard sols eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesWithGramMatrixResidueRing.lean#L74-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesWithGramMatrixResidueRing.lean#L74-L137

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

theorem GlobalTheory.GramCount.ncard_sols_eta [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) (ω : B)
    (hω : IsUnit (ω - c ω)) (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (hB : Fintype.card B = q ^ 2) (n m : ℕ) :
    2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) →
      (1 - 2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n * m - m ^ 2)
          ≤ (Set.ncard (sols c n G) : ℝ) ∧
        (Set.ncard (sols c n G) : ℝ)
          ≤ (1 + 2 * (2 ^ (2 * m + 1) / 2 ^ n)) * (q : ℝ) ^ (2 * n * m - m ^ 2) := by sorry
