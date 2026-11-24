-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_QuotStep_integral_chart_mul_right
-- name    : GlobalTheory.RootEx.QuotStep.integral_chart_mul_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:25:53.618583+00:00
-- url     : https://prove2.me/theorems/9e284558-bb7a-4d2d-83e7-94c5d71cad05
-- title:
--   Quot Step: integral chart mul right
-- statement:
--   The Quot Step construction uses the integral chart mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeilFormulaRootExchangeParabolicIntersection.lean#L182-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeilFormulaRootExchangeParabolicIntersection.lean#L182-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {b : ι → ℕ} {S : ι × ι → Prop}
variable (hS : ∀ rs, S rs → b rs.1 < b rs.2)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.RootEx.QuotStep.integral_chart_mul_right [Fintype {rs // S rs}] (m : GL ι k)
    (hm : ∀ r s, ¬ S (r, s) → m.val r s = (1 : Matrix ι ι k) r s)
    (hm' : ∀ e r s, ¬ S (r, s) → (chart hS e * m).val r s = (1 : Matrix ι ι k) r s)
    (φ : GL ι k → ℂ) (hφ : Continuous φ) :
    ∫ e, φ (chart hS e * m) ∂(Measure.pi fun _ => ν) = ∫ e, φ (chart hS e) ∂(Measure.pi fun _ => ν) := by sorry
