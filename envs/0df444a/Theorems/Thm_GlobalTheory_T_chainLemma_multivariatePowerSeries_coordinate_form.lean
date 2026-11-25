-- Prove2me | Theorems.Thm_GlobalTheory_T_chainLemma_multivariatePowerSeries_coordinate_form
-- name    : GlobalTheory.T.chainLemma_multivariatePowerSeries_coordinate_form
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:48:10.576195+00:00
-- url     : https://prove2.me/theorems/36a5b4b4-312a-4620-b2da-010baad35ce3
-- title:
--   T: chain Lemma multivariate Power Series coordinate form
-- statement:
--   The T construction uses the chain Lemma multivariate Power Series coordinate form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateFormStatement.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateFormStatement.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.chainLemma_multivariatePowerSeries_coordinate_form : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 3 ≤ l → ∀ (d M s₀ : ℕ) (good : Set (Fin d)) (Gs : ℕ → Finset (Fin d)) (al : Fin d → ℕ → Fin d → C) (π : ℕ → Fin d → Fin M → C)
    (t : Fin d → MvPowerSeries (Fin M) C), (∀ s c, c ∈ Gs s → c ∈ good) → (∀ s s' c, s ≤ s₀ → s' ≤ s₀ → c ∈ Gs s → c ∈ Gs s' → s = s') →
    (∀ c e, al c 0 e = if c = e then 1 else 0) → (∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ c ∈ good, al c 1 = 0 ∧ ∀ (n : ℕ) e, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ s < s₀, ∀ c ∈ Gs s, ∀ e, e ∉ Gs (s + 1) → 0 ≤ v (al c 2 e)) →
    (∀ c j, 0 ≤ v (π 0 c j)) → (∀ c, c ∉ Gs 0 → π 0 c = 0) →
    (∀ s e j, π (s + 1) e j = ∑ c ∈ Gs s, (l : C) * al c 2 e * π s c j ^ (l ^ 2)) →
    (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ e, lgSum l al t e = ∑ j, MvPowerSeries.C (R := C) (π 0 e j) * MvPowerSeries.X j) →
    (∀ s ≤ s₀, ∀ c ∈ Gs s, OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c - ∑ j, MvPowerSeries.C (R := C) ((-1) ^ s * ((l : C) ^ (∑ u ∈ Finset.range s, (l ^ 2) ^ u))⁻¹ * π s c j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s)) (1 + 1 / ((l : ℝ) ^ 2 - 1))) ∧
    ∀ c, (∀ s ≤ s₀, c ∉ Gs s) → OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c) (1 + 1 / ((l : ℝ) ^ 2 - 1))) := by sorry
