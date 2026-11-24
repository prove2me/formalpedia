-- Prove2me | Theorems.Thm_GlobalTheory_QuotIntFJ_quotIntFJ_unique
-- name    : GlobalTheory.QuotIntFJ.quotIntFJ_unique
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:45.149548+00:00
-- url     : https://prove2.me/theorems/ee14995e-bb30-4deb-b4a0-60267d478a93
-- title:
--   Quot Int FJ: quot Int FJ unique
-- statement:
--   The Quot Int FJ construction uses the quot Int FJ unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotIntFJUnique.lean#L17-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotIntFJUnique.lean#L17-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProperTriple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotIntFJUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.QuotIntFJ
open GlobalTheory.QuotInt
open MeasureTheory ValuativeRel Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.QuotIntFJ.quotIntFJ_unique : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n]
    [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    (f : GL (n ⊕ Fin c) k → ℂ) (z z' : ℂ), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ ν μX μG ρ f z →
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ ν μX μG ρ f z' → z = z' := by sorry
