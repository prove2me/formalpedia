-- Prove2me | Theorems.Thm_GlobalTheory_OddBlock_expBinomial
-- name    : GlobalTheory.OddBlock.expBinomial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:35:22.644873+00:00
-- url     : https://prove2.me/theorems/dca0bc16-8bd8-466d-bbfb-151d26f56cd7
-- title:
--   Odd Block: exp Binomial
-- statement:
--   The Odd Block construction uses the exp Binomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SumEqOfIsHomogeneous.lean#L680-L685
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SumEqOfIsHomogeneous.lean#L680-L685

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelliStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOneStatement
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NewtonBoundPosAndNewtonStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SumEqOfIsHomogeneous
import Theorems.Thm_GlobalTheory_BlockValue_Lead_prod
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_exp
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_prod

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

theorem GlobalTheory.OddBlock.expBinomial : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 5 ≤ l → ∀ (i E n₀ : ℕ), Odd i → (E : ℝ) = 1 + ((l : ℝ) ^ i - l) / ((l : ℝ) ^ 2 - 1) → ∀ h₁ : MvPowerSeries ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C,
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h₁))) → (∀ α, MvPowerSeries.coeff α h₁ ≠ 0 → ∃ q, α (Sum.inr q) ≠ 0) →
    ∃ Q : ℕ → MvPolynomial (Fin n₀ × Fin n₀) C, Q 0 = 1 ∧ (∀ s, (Q s).IsHomogeneous (n₀ * (l ^ i * s))) ∧
      (∀ s : ℕ, 1 ≤ s → 1 ≤ n₀ → ∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.coeff A (Q s))) ∧
      ∀ y : ℕ, (∑ A ∈ ((MvPolynomial.rename Sum.inl (cayDet n₀ C) ^ (l ^ i * y) * MvPolynomial.rename Sum.inr (cayDet n₀ C) ^ y : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C)).support, MvPolynomial.coeff A ((MvPolynomial.rename Sum.inl (cayDet n₀ C) ^ (l ^ i * y) * MvPolynomial.rename Sum.inr (cayDet n₀ C) ^ y : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C)) * (A.prod fun _ e => (e.factorial : C)) * MvPowerSeries.coeff A (PowerSeries.subst (((∑ q : Fin n₀ × Fin n₀, MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X (Sum.inl q) ^ (l ^ i) * MvPolynomial.X (Sum.inr q) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C) : MvPowerSeries ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C) + h₁) (PowerSeries.exp C))) = (-((l : C) ^ E)⁻¹) ^ (n₀ * y) * ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * (∑ A ∈ (cayDet n₀ C ^ (l ^ i * y)).support, MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * y)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * y - l ^ i * s) * Q s))) := by sorry
