-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_invVol_KO
-- name    : GlobalTheory.FunObj.invVol_KO
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:55.434674+00:00
-- url     : https://prove2.me/theorems/3eedc80b-4b64-4b92-80f6-a10b754e9e1b
-- title:
--   Fun Obj: inv Vol KO
-- statement:
--   The Fun Obj construction uses the inv Vol KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L104-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
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
variable (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c : ℕ)
variable {k n c}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.FunObj.invVol_KO : invVol (KO k (n ⊕ Fin c)) = 1 := by sorry
