-- Prove2me | Theorems.Thm_GlobalTheory_RootExchangeFixed_exUp_fixed_vector
-- name    : GlobalTheory.RootExchangeFixed.exUp_fixed_vector
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:59.647925+00:00
-- url     : https://prove2.me/theorems/d858408d-ba94-4d0c-aa3a-ba2f83413755
-- title:
--   Root Exchange Fixed: ex Up fixed vector
-- statement:
--   The Root Exchange Fixed construction uses the ex Up fixed vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NonarchimedeanLocalFieldSecondCountableT2Space.lean#L200-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NonarchimedeanLocalFieldSecondCountableT2Space.lean#L200-L216

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
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
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.RootExchangeFixed.exUp_fixed_vector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (_ : IsNEquiv ψ p σ l) (v : A), (∀ s : kˣ, (∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v) → (∀ u : n → k, (∀ r, valuation k (u r) ≤ valuation k (s : k)) → σ (rowE c p u) v = v) → exUp ν p σ l v = ((nabs k s ^ Fintype.card n : ℝ) : ℂ) * l v) ∧ ((∀ g ∈ KO k (n ⊕ Fin c), σ g v = v) → exUp ν p σ l v = l v) := by sorry
