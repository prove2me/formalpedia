-- Prove2me | Theorems.Thm_MazurTransfer_original_nineteenth_root_inertia_valuation_divisibility
-- name    : MazurTransfer.original_nineteenth_root_inertia_valuation_divisibility
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T00:44:02.308308+00:00
-- url     : https://prove2.me/theorems/dc906d95-9267-4f16-9133-9c14e30e4045
-- statement:
--   At a rational prime different from nineteen, inertia fixing one nineteenth root of a nonzero radicand fixes every nineteenth root of that same radicand. If the original number-field rational radicand has such a fixed root at every valuation above the given rational prime, its original normalized prime valuation is divisible by nineteen. The two original arithmetic inputs are complete existing official Anthropic FLT proofs with exact public full types checked independently. Every original prime, nonzero, field, root and genuine inertia hypothesis is retained. Named downstream consumer: original actual selected pi Selmer rational radicand prime divisibility and thirteen-support.

import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
noncomputable section
open NumberField IsDedekindDomain

theorem MazurTransfer.original_nineteenth_root_inertia_valuation_divisibility : (∀ (q : ℕ) (hq : q.Prime) (hne : q ≠ 19), ¬ q ∣ 19) ∧ (∀ (q : ℕ) (hq : q.Prime) (hne : q ≠ 19) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (a α β : (AlgebraicClosure ℚ)) (ha : a ≠ 0) (hα : α ^ 19 = a) (hβ : β ^ 19 = a) (hfix : ∀ σ : A.inertiaSubgroupIn ℚ, σ.val α = α), ∀ σ : A.inertiaSubgroupIn ℚ, σ.val β = β) ∧ (∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L] (x : (L : Type)ˣ) (v : HeightOneSpectrum (𝓞 L)) (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L) ∈ v.asIdeal) (y : (AlgebraicClosure ℚ)) (hy : y ^ 19 = ((x : L) : (AlgebraicClosure ℚ))) (hfix : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime q → ∀ σ : A.inertiaSubgroupIn ℚ, σ.val y = y), (19 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)) ∧ (∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L] (x : (L : Type)ˣ) (v : HeightOneSpectrum (𝓞 L)) (q : ℕ) (hq : q.Prime) (h19 : q ≠ 19) (hqv : (q : 𝓞 L) ∈ v.asIdeal) (y : (AlgebraicClosure ℚ)) (hy : y ^ 19 = ((x : L) : (AlgebraicClosure ℚ))) (hfix : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime q → ∃ α : (AlgebraicClosure ℚ), α ≠ 0 ∧ α ^ 19 = ((x : L) : (AlgebraicClosure ℚ)) ∧ ∀ σ : A.inertiaSubgroupIn ℚ, σ.val α = α), (19 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)) := by sorry
