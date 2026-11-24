-- Prove2me | Theorems.Thm_GlobalTheory_HeisLine_form_eq_ell
-- name    : GlobalTheory.HeisLine.form_eq_ell
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:18:14.114348+00:00
-- url     : https://prove2.me/theorems/ac3ac1b6-aca1-49ae-b763-d9593046fe7b
-- title:
--   Heis Line: form eq ell
-- statement:
--   The Heis Line construction uses the form eq ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AddCharDotProductTrivialOnTsupportNhds.lean#L311-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AddCharDotProductTrivialOnTsupportNhds.lean#L311-L325

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
variable (hχ : HasConductor χ c) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (h2 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) →
      (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b')
include hχ h2

theorem GlobalTheory.HeisLine.form_eq_ell (a b : SB (n → k))
    (hm : (fun η => (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η) ∈ SB (n → k)) :
    B a b = ell χ μ B ⟨_, hm⟩ := by sorry
