-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_UnfModel_elt_one
-- name    : GlobalTheory.FunObj.UnfModel.elt_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:28.948366+00:00
-- url     : https://prove2.me/theorems/46b49812-26a6-43df-ba2c-ad3f4f6ee078
-- title:
--   Unf Model: elt one
-- statement:
--   The Unf Model construction uses the elt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L55-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
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
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid k} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.FunObj.UnfModel.elt_one (J : G.Level) :
    (Reps.through hs J fun _ => 1).elt (fun _ => DoubleCoset.mk _ _ 1) = 1 := by sorry
