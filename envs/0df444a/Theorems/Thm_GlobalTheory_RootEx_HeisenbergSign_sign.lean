-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_HeisenbergSign_sign
-- name    : GlobalTheory.RootEx.HeisenbergSign.sign
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:37.355369+00:00
-- url     : https://prove2.me/theorems/f00ba13a-cf13-4b1c-98ad-5dab75891628
-- title:
--   Heisenberg Sign: sign
-- statement:
--   The Heisenberg Sign construction uses the sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeHeisenbergVariableSign.lean#L23-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeHeisenbergVariableSign.lean#L23-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeHeisenbergVariableSign
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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.HeisenbergSign

theorem GlobalTheory.RootEx.HeisenbergSign.sign : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) (β : n → k) (r : n) (i : Fin (c + 1)), i.val + 1 = ρ + 1 → ((1 - ((colE c (ρ + 1) β).val - 1)) * affPt (ρ + 1) x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (Sum.inl r) (Sum.inr i) = -β r) ∧ ∀ (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (β : n → k), (∀ x, om μ 1 (colE c (ρ + 1) β) Φ.1 x = Φ.1 ((1 - ((colE c (ρ + 1) β).val - 1)) * x)) ∧ ∀ x₀, fl ψ ν μ ρ Φ.1 x₀ β = opE ψ ν (ρ + 1) (fun x => Φ.1 (x + colM c (ρ + 1) (-β))) x₀ := by sorry
