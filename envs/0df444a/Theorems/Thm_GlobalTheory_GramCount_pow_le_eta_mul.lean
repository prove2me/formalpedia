-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_pow_le_eta_mul
-- name    : GlobalTheory.GramCount.pow_le_eta_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:28:23.916337+00:00
-- url     : https://prove2.me/theorems/7abe7e4f-8fb6-5e27-8843-e3d14cb2d3ca
-- title:
--   Gram Count: pow le eta mul
-- statement:
--   The Gram Count construction uses the pow le eta mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesWithGramMatrixResidueRing.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesWithGramMatrixResidueRing.lean#L57-L66

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

theorem GlobalTheory.GramCount.pow_le_eta_mul {q m n : ℕ} (hq : 2 ≤ q) (h : 2 * m + 1 ≤ n) :
    (q : ℝ) ^ n ≤ (2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n - (2 * m + 1)) := by sorry
