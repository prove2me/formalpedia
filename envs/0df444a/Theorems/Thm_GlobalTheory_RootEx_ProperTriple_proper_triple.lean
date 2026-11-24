-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ProperTriple_proper_triple
-- name    : GlobalTheory.RootEx.ProperTriple.proper_triple
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:24.961009+00:00
-- url     : https://prove2.me/theorems/8c80b877-f5fc-4f2b-8ba7-a6f043bcd135
-- title:
--   Proper Triple: proper triple
-- statement:
--   The Proper Triple construction uses the proper triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ProperTriple.lean#L70-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ProperTriple.lean#L70-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProperTriple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ProperTriple
open MeasureTheory ValuativeRel Matrix

theorem GlobalTheory.RootEx.ProperTriple.proper_triple : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ)
    (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C),
    ∃ D : Set (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k)), IsCompact D ∧
      ∀ z : GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k),
        _root_.GlobalTheory.RootEx.embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) *
          _root_.GlobalTheory.RootEx.colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by sorry
