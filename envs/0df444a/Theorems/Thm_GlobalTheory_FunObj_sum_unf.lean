-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_sum_unf
-- name    : GlobalTheory.FunObj.sum_unf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:46.832906+00:00
-- url     : https://prove2.me/theorems/d54ce279-b8ed-443e-8a2b-256bdfa81c00
-- title:
--   Fun Obj: sum unf
-- statement:
--   The Fun Obj construction uses the sum unf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L299-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L299-L301

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

theorem GlobalTheory.FunObj.sum_unf (hfin : (unfSupport ψ ν keep ρ T).Finite) (f : UnfTerm G → ℂ) :
    ((unf ψ ν keep ρ T hfin).map f).sum = ∑ᶠ β ∈ unfSupport ψ ν keep ρ T, f (unfTerm ψ ν keep ρ T β) := by sorry
