-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_diagonal_uniform
-- name    : OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:31:36.934991+00:00
-- url     : https://prove2.me/theorems/370f516c-9045-4b6f-8a0d-3af327f05158
-- title:
--   OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingInitialDiagonalUniform.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingInitialDiagonalUniform.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.moving_selected_initial_diagonal_uniform
--       (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
--       (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (r : Fin k → ℕ) (hk : 0 < k)
--       (A Wwin Bφ Dφ c K εdiag Bs BD Bz B : ℝ)
--       (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
--       (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
--       (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
--       (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
--       (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
--       (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD) (hBz : 9 ≤ Bz)
--       (hmassBudget : ∀ i, 4 * (K + 1) * r i ≤ (k : ℝ) ^ 4)
--       (hBD : Bs + 2 * B +
--         (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
--       ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
--       ∀ᶠ L : ℝ in atTop, ∀ depth : Fin k, ∀ b : ℕ, spectatorBulkCount k L = b + b →
--         let m := b + b
--         let Cprior := K + 1
--         ∀ (tierB : MovingRegularSlot depth.val (r depth) m → ℕ)
--           (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
--           (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
--           (childBound pivotBound V : ℕ → ℕ)
--           (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
--           (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
--           (β : Fin m → ℝ)
--           (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
--           (φ : ℝ → ℝ) (G : ℕ → ℝ)
--           (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot depth.val (r depth) m → Finset ℕ)
--           (setsReg : ∀ q : ℕ, Finset (ZMod q))
--           (cb cd btop : ℝ) (lower : TreeLeafIndex depth.val × Fin (r depth) → ℝ)
--           (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
--         let H := G (depth.val + 1)
--         let slot := movingTemplateBulk depth.val (r depth) m
--         let μ := fun j => primeSubsetPrior primes (Qμ j)
--         let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
--           (Real.exp ((6 / 1000 : ℝ) * L))
--         let Sfreq := (transferFrequencyRange (V depth.val)).erase 0
--         4 + (r depth) + 4 * depth.val = rinit + rinit →
--         Monotone V →
--         (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
--         (V depth.val : ℝ) ≤ Real.exp (A * m) →
--         (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
--         0 ≤ Δ → Δ ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
--         1 ≤ H - 1 →
--         (∀ i, depth.val ≤ tierB i) →
--         1 ≤ m → (∀ i, primeCutoff ≤ p i) →
--         (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
--         (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
--         (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
--         (∀ i, residueDensity (sets i) ≤ 2 / 3) →
--         (∀ i, 2 * β i ≤ ε) →
--         (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
--           ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
--         (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
--         (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
--         ((global.card + (Fintype.card (MovingRegularSlot depth.val (4 + (r depth)) m) + 4 * depth.val * 2 ^ depth.val) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
--         (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
--         (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
--         (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
--         (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
--         (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
--         (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
--         (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
--         (∀ j, j ≤ depth.val → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
--         (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
--         V depth.val ≤ primeLo → V depth.val < cutoff → cutoff ≤ primeLo →
--         (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
--         (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
--         (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
--         (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
--         (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
--         (∀ q ∈ Qμ depth.val, (q : ℝ) ≤ Real.exp btop) →
--         (∀ x, φ x ≤ 1) →
--         (∀ j : TreeLeafIndex depth.val × Fin (r depth), ∀ q : primes,
--           (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
--         (∀ j (q : primes), (q : ℕ) ∈ Qν j → V depth.val < (q : ℕ)) →
--         (∀ q : smoothGiantPrimeRange H, smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0 →
--           ∀ j (z : primes), (z : ℕ) ∈ Qν j → (q : ℕ) ≠ (z : ℕ)) →
--         (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
--           ((2 ^ depth.val * 4 : ℕ) : ℝ) * btop -
--             ((∑ j, lower j) + (2 ^ depth.val : ℕ) * (2 * cb - 2)) ≤
--           -spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ depth.val : ℕ) m) →
--         movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
--           (movingOriginalLeaf Subtype.val p
--             (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
--             (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
--           φ G depth.val (r depth) m (smoothGiantPrimeRange H)
--           (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
--           (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
--           (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
--         Real.exp (-(2 * B + 3) * (2 ^ depth.val : ℕ) * m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveRealZero` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.MovingRegularSlot`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.logCellProfile`, `OAI.Ostmann.movingTemplateBulk`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.residueDensity`, `OAI.Ostmann.transferFrequencyRange` and `OAI.Ostmann.treeLeafIndexFintype` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.bulkProgressionCutoff`, `OAI.Ostmann.deletedConductorPrime`, `OAI.Ostmann.giantProgressionCutoff`, `OAI.Ostmann.smoothGiantLogNormalizer`, `OAI.Ostmann.smoothGiantPrimeRange`, `OAI.Ostmann.smoothGiantPrior`, `OAI.Ostmann.spectatorBaseGap`, `OAI.Ostmann.spectatorBulkCount` and `OAI.Ostmann.spectatorStepGap` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.initialMovingDataCutoff`, `OAI.Ostmann.movingAmplitudeDiagonal` and `OAI.Ostmann.normalizedResidueTransform` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.selectedPageZero` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.normalizedResidueFamily` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalLeaf` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.PublishedProgressionInput.selected_scheduled_diagonal` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingInitialDiagonalUniform.lean (declaration OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform)

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
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_diagonal_uniform
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (r : Fin k → ℕ) (hk : 0 < k)
    (A Wwin Bφ Dφ c K εdiag Bs BD Bz B : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD) (hBz : 9 ≤ Bz)
    (hmassBudget : ∀ i, 4 * (K + 1) * r i ≤ (k : ℝ) ^ 4)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ depth : Fin k, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot depth.val (r depth) m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot depth.val (r depth) m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd btop : ℝ) (lower : TreeLeafIndex depth.val × Fin (r depth) → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let H := G (depth.val + 1)
      let slot := movingTemplateBulk depth.val (r depth) m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V depth.val)).erase 0
      4 + (r depth) + 4 * depth.val = rinit + rinit →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V depth.val : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, depth.val ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot depth.val (4 + (r depth)) m) + 4 * depth.val * 2 ^ depth.val) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ depth.val → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V depth.val ≤ primeLo → V depth.val < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (∀ q ∈ Qμ depth.val, (q : ℝ) ≤ Real.exp btop) →
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex depth.val × Fin (r depth), ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → V depth.val < (q : ℕ)) →
      (∀ q : smoothGiantPrimeRange H, smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0 →
        ∀ j (z : primes), (z : ℕ) ∈ Qν j → (q : ℕ) ≠ (z : ℕ)) →
      (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
        ((2 ^ depth.val * 4 : ℕ) : ℝ) * btop -
          ((∑ j, lower j) + (2 ^ depth.val : ℕ) * (2 * cb - 2)) ≤
        -spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ depth.val : ℕ) m) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G depth.val (r depth) m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      Real.exp (-(2 * B + 3) * (2 ^ depth.val : ℕ) * m) := by
  sorry

end Ostmann

end OAI
end
