-- Prove2me | Theorems.Thm_GlobalTheory_HeisLine_heis_invariant_form
-- name    : GlobalTheory.HeisLine.heis_invariant_form
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:18.972741+00:00
-- url     : https://prove2.me/theorems/3e10ad90-c96c-4395-a08b-bc5424f90e17
-- title:
--   Heis Line: heis invariant form
-- statement:
--   The Heis Line construction uses the heis invariant form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AddCharDotProductTrivialOnTsupportNhds.lean#L329-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AddCharDotProductTrivialOnTsupportNhds.lean#L329-L352

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AddCharDotProductTrivialOnTsupportNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.HeisLine
open GlobalTheory.SplitWeil.FourierPi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]
variable [MeasurableSpace k] [BorelSpace k]
variable {χ : AddChar k Circle} {c : kˣ}

theorem GlobalTheory.HeisLine.heis_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] (χ : AddChar k Circle), Continuous χ → χ ≠ 1 → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ), (∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = (χ (t ⬝ᵥ y) : ℂ) * a.1 y) → (∀ η, b'.1 η = b.1 (η - t)) → B a' b = B a b') → (∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) → (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b') → ∃ c : ℂ, ∀ a b : SB (n → k), B a b = c * ∫ η, (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η ∂μ := by sorry
