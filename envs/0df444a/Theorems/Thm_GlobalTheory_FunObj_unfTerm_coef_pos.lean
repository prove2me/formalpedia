-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_unfTerm_coef_pos
-- name    : GlobalTheory.FunObj.unfTerm_coef_pos
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:40.654802+00:00
-- url     : https://prove2.me/theorems/0ffaa459-9852-42b0-97d7-5a982ebde5b2
-- title:
--   Fun Obj: unf Term coef pos
-- statement:
--   The Fun Obj construction uses the unf Term coef pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L312-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L312-L324

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
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable {hs}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
variable {J : G.Level} (keep : Bool) (ρ : Reps hs J) (T : G.Args → ℂ)

theorem GlobalTheory.FunObj.unfTerm_coef_pos (hJ : ∀ j, 0 < j → j < G.m → IsOpen (J (G.m, j) : Set (GL (Fin (G.rank (G.m, j))) k)) ∧
    J (G.m, j) ≤ KO k _) (β : Cosets hs J) : 0 < (unfTerm ψ ν keep ρ T β).coef := by sorry
