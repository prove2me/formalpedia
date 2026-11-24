-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_integral_comp_mul_mul_volM
-- name    : GlobalTheory.SplitWeil.integral_comp_mul_mul_volM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:07.887312+00:00
-- url     : https://prove2.me/theorems/a7b1ab92-60b9-4a77-9b44-2ea9d4ae4fb6
-- title:
--   Split Weil: integral comp mul mul vol M
-- statement:
--   The Split Weil construction uses the integral comp mul mul vol M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LinearChangeOfVariablesLocalFieldMatrix.lean#L166-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LinearChangeOfVariablesLocalFieldMatrix.lean#L166-L188

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

theorem GlobalTheory.SplitWeil.integral_comp_mul_mul_volM (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) =
      (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by sorry
