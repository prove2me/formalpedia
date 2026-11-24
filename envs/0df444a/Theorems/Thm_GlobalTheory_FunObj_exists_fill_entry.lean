-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_exists_fill_entry
-- name    : GlobalTheory.FunObj.exists_fill_entry
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:41:59.285924+00:00
-- url     : https://prove2.me/theorems/2119238f-2567-4d9b-8a58-7d6f73ca87c6
-- title:
--   Fun Obj: exists fill entry
-- statement:
--   The Fun Obj construction uses the exists fill entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L65-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.FunObj.exists_fill_entry (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) (j : Fin (G.m - 1))
    (rs : StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) :
    ∃ a b c, ∀ e : Vars G, e j rs = fill hs x y e (.theta G.m j) a b - c := by sorry
