-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_keptPart_joinVars
-- name    : GlobalTheory.FunObj.keptPart_joinVars
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:50.539805+00:00
-- url     : https://prove2.me/theorems/052b1395-a3dd-408a-8c0e-825278ca7b12
-- title:
--   Fun Obj: kept Part join Vars
-- statement:
--   The Fun Obj construction uses the kept Part join Vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L113-L115

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
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}
omit [Field k]

theorem GlobalTheory.FunObj.keptPart_joinVars (w : KeptVar n c n' → k) (f : FreeVar n c n' → k) : keptPart (joinVars (w, f)) = w := by sorry
