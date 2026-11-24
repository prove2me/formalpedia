-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_linear_change_of_variables
-- name    : GlobalTheory.SplitWeil.linear_change_of_variables
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:46.919801+00:00
-- url     : https://prove2.me/theorems/81478206-a99f-4f68-81d2-ecd8e7265327
-- title:
--   Split Weil: linear change of variables
-- statement:
--   The Split Weil construction uses the linear change of variables property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LinearChangeOfVariablesLocalFieldMatrix.lean#L190-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LinearChangeOfVariablesLocalFieldMatrix.lean#L190-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.SplitWeil.linear_change_of_variables : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by sorry
