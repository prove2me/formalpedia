-- Prove2me | Theorems.Thm_OAI_Ostmann_movingTemplatePrimeAmplitude_step_full_coefficients
-- name    : OAI.Ostmann.movingTemplatePrimeAmplitude_step_full_coefficients
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:32:22.663494+00:00
-- url     : https://prove2.me/theorems/86ced78e-d802-4402-9bf3-4b186c437ffc
-- title:
--   OAI.Ostmann.movingTemplatePrimeAmplitude_step_full_coefficients: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.movingTemplatePrimeAmplitude_step_full_coefficients` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingFullCoefficientTransfer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingFullCoefficientTransfer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical BigOperators ComplexConjugate`):
--
--   ```lean
--   theorem movingTemplatePrimeAmplitude_step_full_coefficients {σ J : Type} [Fintype σ]
--       (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
--       (outside : List ℕ) (μ : ℕ → σ → ℝ)
--       (childBound pivotBound V : ℕ → ℕ)
--       (q : J → ℕ) [∀ i, Fact (q i).Prime]
--       (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
--       (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
--       (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
--       (ψ : SchwartzMap ℝ ℂ) (X lo hi W : ℝ) (hX : 0 < X)
--       (hwindow : X * hi ≤ Real.exp W)
--       (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
--       (hμlower : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
--       (n r m : ℕ) (Y reserveMass : ℝ) (hm : 64 ≤ reserveMass) (hY : Y ≤ W)
--       (hVeq : V = movingProductNaturalCutoff (movingCellPivotExponent G c) W Y reserveMass)
--       (hbudget : ∀ j, 2 * movingCellPivotExponent G c j ≤
--         movingProductExponent (movingCellPivotExponent G c) W j)
--       (hpositive : 0 ≤ movingProductExponent (movingCellPivotExponent G c) W n -
--         movingCellPivotExponent G c n)
--       (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : smoothGiantLivePrimes Pg φ (G (n + 1)) ⊆ I)
--       (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
--       (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
--       (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
--       (ν : MovingRegularSlot n r m → σ → ℝ)
--       (sets : ∀ q : ℕ, Finset (ZMod q))
--       (hsets : ∀ a, (sets (value a)).Nonempty)
--       (hcard : ∀ a, (sets (value a)).card < value a)
--       (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
--       (hgiant : ∀ q : smoothGiantLivePrimes Pg φ (G (n + 1)), ∀ x, ggiant q (-x) = conj (ggiant q x))
--       (H : ℕ)
--       (hHeq : H = ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
--         movingCellPivotExponent G c n)⌉₊)
--       (hIlower : ∀ p ∈ I, Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
--       (hlarge : ∀ (q : smoothGiantLivePrimes Pg φ (G (n + 1))) (y : MovingRegularSlot n r m → σ),
--         (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
--       (hvg : ∀ q : smoothGiantLivePrimes Pg φ (G (n + 1)), V (n + 1) < (q : ℕ))
--       (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
--       (hchild : V n ≤ childBound (n + 1))
--       (hgap : ∀ XR : smoothGiantLivePrimes Pg φ (G (n + 1)), ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
--         ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
--         ∀ (p : ℕ) (w : ℤ),
--         movingTemplateCoefficient value outside μ childBound pivotBound V (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m w
--           (movingRestoreSample n r m u right) p XR ≠ 0 →
--         2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
--       (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
--         (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
--         (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
--       let ρ := smoothGiantPrior Pg φ (G (n + 1))
--       let greg := normalizedResidueFamily sets
--       Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
--         ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
--           (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m
--           Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
--         movingAmplitudeDiagonal value outside μ childBound pivotBound V
--           (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg I
--           ρ ν greg ggiant favorable +
--         ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
--           (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G (n + 1) r m
--           Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MovingRegularSlot`, `OAI.Ostmann.MovingSlotData`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.movingRestoreSample` and `OAI.Ostmann.treeLeafIndexFintype` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.movingCellPivotExponent`, `OAI.Ostmann.movingProductExponent`, `OAI.Ostmann.movingProductNaturalCutoff`, `OAI.Ostmann.smoothGiantLivePrimes`, `OAI.Ostmann.smoothGiantLogNormalizer`, `OAI.Ostmann.smoothGiantMass` and `OAI.Ostmann.smoothGiantPrior` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.movingAmplitudeDiagonal` and `OAI.Ostmann.movingTemplateCoefficient` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.movingTemplateDoubledPrior` and `OAI.Ostmann.movingTemplateRestoredPrior` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.movingTemplatePrimeAmplitude` and `OAI.Ostmann.normalizedResidueFamily` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalLeaf` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.selected_scheduled_iteration` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingFullCoefficientTransfer.lean (declaration OAI.Ostmann.movingTemplatePrimeAmplitude_step_full_coefficients)

import Mathlib
import Definitions.Def_OAIQ095D008

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingTemplatePrimeAmplitude_step_full_coefficients {σ J : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμlower : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n r m : ℕ) (Y reserveMass : ℝ) (hm : 64 ≤ reserveMass) (hY : Y ≤ W)
    (hVeq : V = movingProductNaturalCutoff (movingCellPivotExponent G c) W Y reserveMass)
    (hbudget : ∀ j, 2 * movingCellPivotExponent G c j ≤
      movingProductExponent (movingCellPivotExponent G c) W j)
    (hpositive : 0 ≤ movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : smoothGiantLivePrimes Pg φ (G (n + 1)) ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : smoothGiantLivePrimes Pg φ (G (n + 1)), ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hHeq : H = ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊)
    (hIlower : ∀ p ∈ I, Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (hlarge : ∀ (q : smoothGiantLivePrimes Pg φ (G (n + 1))) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : smoothGiantLivePrimes Pg φ (G (n + 1)), V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : smoothGiantLivePrimes Pg φ (G (n + 1)), ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  sorry

end Ostmann

end OAI
end
