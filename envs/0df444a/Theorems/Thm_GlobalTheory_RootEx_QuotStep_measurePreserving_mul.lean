-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_QuotStep_measurePreserving_mul
-- name    : GlobalTheory.RootEx.QuotStep.measurePreserving_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:41.216286+00:00
-- url     : https://prove2.me/theorems/23a43598-8690-41e9-9af6-b5f3b8db2add
-- title:
--   Quot Step: measure Preserving mul
-- statement:
--   The Quot Step construction uses the measure Preserving mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeilFormulaRootExchangeParabolicIntersection.lean#L213-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeilFormulaRootExchangeParabolicIntersection.lean#L213-L289

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

theorem GlobalTheory.RootEx.QuotStep.measurePreserving_mul {n : Type} [Fintype n] [Fintype {rs // S rs}]
    [Fintype {rs : ι × ι // b rs.1 < b rs.2}] (j : n → ι × ι) (hj : Function.Injective j)
    (hjS : ∀ x, ¬ S (j x)) (hjb : ∀ x, b (j x).1 < b (j x).2)
    (hcov : ∀ rs, b rs.1 < b rs.2 → S rs ∨ ∃ x, j x = rs)
    (E : (n → k) → GL ι k) (hE : ∀ β x, (E β).val (j x).1 (j x).2 = β x)
    (hE' : ∀ β r s, (∀ x, j x ≠ (r, s)) → (E β).val r s = (1 : Matrix ι ι k) r s) :
    MeasurePreserving (fun (y : (n → k) × ({rs // S rs} → k)) (i : {rs : ι × ι // b rs.1 < b rs.2}) =>
        (chart hS y.2 * E y.1).val i.1.1 i.1.2)
      ((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) (Measure.pi fun _ => ν) := by sorry
