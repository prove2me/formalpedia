-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_keptRow_eq
-- name    : GlobalTheory.FunObj.keptRow_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:15.115661+00:00
-- url     : https://prove2.me/theorems/b3cae836-388e-4536-bb43-97cba30d94ec
-- title:
--   Fun Obj: kept Row eq
-- statement:
--   The Fun Obj construction uses the kept Row eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L200-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L200-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}

theorem GlobalTheory.FunObj.keptRow_eq (x : ColArgs G) (w : KeptVars G) (j : Fin (G.m - 1)) (hj : Odd (G.m - 2 - j))
    (s : Fin (topRank G j)) : keptRow x w j s =
      w j ⟨(.inr ⟨(G.m - 2 - j) / 2, by have := hj.pos; omega⟩, .inl s), hj, rfl⟩ := by sorry
