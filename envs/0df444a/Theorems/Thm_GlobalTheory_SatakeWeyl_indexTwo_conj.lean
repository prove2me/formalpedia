-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_indexTwo_conj
-- name    : GlobalTheory.SatakeWeyl.indexTwo_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:48:32.268286+00:00
-- url     : https://prove2.me/theorems/ffda863a-e9e8-4885-b5f5-08a7c69c796b
-- title:
--   Satake Weyl: index Two conj
-- statement:
--   The Satake Weyl construction uses the index Two conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankTwoRootIndexOfTraceZeroCard.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankTwoRootIndexOfTraceZeroCard.lean#L53-L61

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankTwoRootIndexOfTraceZeroCard
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem GlobalTheory.SatakeWeyl.indexTwo_conj {ϖ : L} (h0 : ϖ ≠ 0) (s g : GU σ 2)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ (![1, -1] : Fin 2 → ℤ) i)) (y : L)
    (h : mat g = !![1, y; 0, 1]) : mat (s * g * s⁻¹) = !![1, ϖ * (ϖ * y); 0, 1] := by sorry
