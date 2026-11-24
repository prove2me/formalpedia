-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Shear_lintegral_shear_eq
-- name    : GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:47.292849+00:00
-- url     : https://prove2.me/theorems/d4e02184-87ab-4819-861a-e5037f7f8f6c
-- title:
--   Shear: lintegral shear eq
-- statement:
--   The Shear construction uses the lintegral shear eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuotientMeasureByInvariantSubgroup.lean#L8-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuotientMeasureByInvariantSubgroup.lean#L8-L63

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuotientMeasureByInvariantSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Shear

theorem GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V]
    [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V]
    (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant]
    [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f →
    (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ →
    ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by sorry
