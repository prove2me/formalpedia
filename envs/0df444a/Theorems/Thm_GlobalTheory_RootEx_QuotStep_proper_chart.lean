-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_QuotStep_proper_chart
-- name    : GlobalTheory.RootEx.QuotStep.proper_chart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:49.583731+00:00
-- url     : https://prove2.me/theorems/637abb42-ae2f-4694-ae52-189932a0cf1d
-- title:
--   Quot Step: proper chart
-- statement:
--   The Quot Step construction uses the proper chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeilFormulaRootExchangeParabolicIntersection.lean#L378-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeilFormulaRootExchangeParabolicIntersection.lean#L378-L400

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
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RootEx.QuotStep.proper_chart {q : ℕ} {b : n ⊕ Fin c → ℕ} {S : (n ⊕ Fin c) × (n ⊕ Fin c) → Prop}
    (hS : ∀ rs, S rs → b rs.1 < b rs.2) (hq : ∀ e, (chart hS e : GL (n ⊕ Fin c) k) ∈ N k n c q)
    (C : Set (GL (n ⊕ Fin c) k)) (hC : IsCompact C) :
    ∃ D, IsCompact D ∧ ∀ t : GL n k × ({rs // S rs} → k), embX c t.1 * chart hS t.2 ∈ C → t ∈ D := by sorry
