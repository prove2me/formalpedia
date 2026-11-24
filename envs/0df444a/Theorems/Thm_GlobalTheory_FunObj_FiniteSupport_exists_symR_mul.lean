-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_exists_symR_mul
-- name    : GlobalTheory.FunObj.FiniteSupport.exists_symR_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:40:42.717632+00:00
-- url     : https://prove2.me/theorems/3f0e373c-b674-4ae5-a8f7-f39e5356c50d
-- title:
--   Finite Support: exists sym R mul
-- statement:
--   The Finite Support construction uses the exists sym R mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L67-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L67-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [Fintype n']

theorem GlobalTheory.FunObj.FiniteSupport.exists_symR_mul (hc : 1 ≤ c) (ψ : AddChar k Circle) {γ δ : ValueGroupWithZero k} (hγ : 1 ≤ γ)
    (hψ : ∀ a : k, (∀ t, valuation k t ≤ δ → ψ (a * t) = 1) → valuation k a ≤ γ)
    (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k)
    (h1 : Bd γ ((h⁻¹).val * stepPt x₀ e))
    (h2 : ∀ d : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k, (∀ r s, ¬ Free (c / 2 + 1) (r, s) → d r s = 0) →
      (∀ r s, d r (Sum.inl s) = 0) → Bd δ ((h⁻¹).val * d) → ψ (ch d) = 1) :
    ∃ r ∈ symR k n c, ∃ w : GL (n ⊕ Fin c) k, Bd (γ * γ) w.val ∧ Bd (γ * γ) (w⁻¹).val ∧ h = r * w := by sorry
