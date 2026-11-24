-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_of_isQuotIntFJ_of_isQuotIntFJ
-- name    : GlobalTheory.T.eq_of_isQuotIntFJ_of_isQuotIntFJ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:33:19.1168+00:00
-- url     : https://prove2.me/theorems/e0dc48f6-e66e-49ac-a164-296155a47af3
-- title:
--   T: eq of is Quot Int FJ of is Quot Int FJ
-- statement:
--   The T construction uses the eq of is Quot Int FJ of is Quot Int FJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotIntFJUniqueStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotIntFJUniqueStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotIntFJUnique
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotIntFJUniqueStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_of_isQuotIntFJ_of_isQuotIntFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ) (z z' : ℂ), IsQuotIntFJ ν μX μG ρ f z → IsQuotIntFJ ν μX μG ρ f z' → z = z' := by sorry
