-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_continuous_fill
-- name    : GlobalTheory.FunObj.continuous_fill
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:42:04.68578+00:00
-- url     : https://prove2.me/theorems/1f692aa4-1140-4496-b295-a1cec85bea84
-- title:
--   Fun Obj: continuous fill
-- statement:
--   The Fun Obj construction uses the continuous fill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L37-L46

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

theorem GlobalTheory.FunObj.continuous_fill (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) : Continuous (fill hs x y) := by sorry
