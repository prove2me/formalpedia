-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_isNEquiv_integral
-- name    : GlobalTheory.RootEx.Exchange.isNEquiv_integral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:24:01.768145+00:00
-- url     : https://prove2.me/theorems/bf860625-0011-4916-a6d8-4b4d9a425396
-- title:
--   Exchange: is NEquiv integral
-- statement:
--   The Exchange construction uses the is NEquiv integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegrableOfMemSB.lean#L189-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegrableOfMemSB.lean#L189-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  (ν : Measure k) [ν.IsAddHaarMeasure] {A : Type} [AddCommGroup A] [Module ℂ A]

theorem GlobalTheory.RootEx.Exchange.isNEquiv_integral {ψ : AddChar k Circle} {p q : ℕ} {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
    {l : A → ℂ} (hl : IsNEquiv ψ p σ l) (E : (n → k) → GL (n ⊕ Fin c) k)
    (hE : ∀ g ∈ N k n c q, ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c p, simpleSum h = simpleSum g ∧
      E u * g = h * E (u + w)) :
    IsNEquiv ψ q σ fun v => ∫ u, l (σ (E u) v) ∂(Measure.pi fun _ => ν) := by sorry
