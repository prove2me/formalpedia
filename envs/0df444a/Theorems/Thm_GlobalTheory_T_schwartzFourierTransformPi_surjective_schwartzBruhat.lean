-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartzFourierTransformPi_surjective_schwartzBruhat
-- name    : GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:42.069813+00:00
-- url     : https://prove2.me/theorems/771437e9-c482-4e3c-b891-114424f5c892
-- title:
--   T: schwartz Fourier Transform Pi surjective schwartz Bruhat
-- statement:
--   The T construction uses the schwartz Fourier Transform Pi surjective schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzFourierTransformPiSurjectiveSchwartzBruhStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzFourierTransformPiSurjectiveSchwartzBruhStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzFourierTransformPiSurjectiveSchwartzBruh
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzFourierTransformPiSurjectiveSchwartzBruhStatement
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

theorem GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by sorry
