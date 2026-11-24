-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_keptCol_eq
-- name    : GlobalTheory.FunObj.keptCol_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:30.345808+00:00
-- url     : https://prove2.me/theorems/99643360-d7cc-48aa-9e5f-a361a37da603
-- title:
--   Fun Obj: kept Col eq
-- statement:
--   The Fun Obj construction uses the kept Col eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L197-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L197-L198

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

theorem GlobalTheory.FunObj.keptCol_eq (w : KeptVars G) (j : Fin (G.m - 1)) (hj : Even (G.m - 2 - j)) (r : Fin (topRank G (j + 1))) :
    keptCol w j r = w j ⟨(.inl r, .inr ⟨(G.m - 2 - j) / 2, by omega⟩), hj, rfl⟩ := by sorry
