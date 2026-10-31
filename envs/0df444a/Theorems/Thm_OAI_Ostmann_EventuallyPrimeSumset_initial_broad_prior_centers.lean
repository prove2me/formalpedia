-- Prove2me | Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_initial_broad_prior_centers
-- name    : OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:19:29.377569+00:00
-- url     : https://prove2.me/theorems/c5c8c1a2-ce52-49aa-b809-e0d6610c50db
-- title:
--   OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers` of [lean/OAI/NumberTheory/Ostmann/Construction/TailInitialBroadPriors.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/TailInitialBroadPriors.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem EventuallyPrimeSumset.initial_broad_prior_centers
--       (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
--       (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
--       (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
--       {C : ℝ} (hM : MertensEstimate C)
--       {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
--       (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
--       (k cutoff : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
--       ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
--         Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
--         ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
--         ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
--         let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
--           (Real.exp ((6 / 1000 : ℝ) * L)) \ D
--         let m := spectatorBulkCount k L
--         let good := fun p : ℕ => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
--           residueDensity (tailDensityMask A N p) ≤ 2 / 3
--         ∃ Qd : Finset ℕ,
--           Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
--             (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
--           L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
--           (∀ p ∈ Qd, cutoff ≤ p ∧ good p ∧ tailCharacterBias A N p ≤ ε / 2) ∧
--           ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → Qb ⊆ P → Qd ⊆ P →
--             (∑ p : P, primeSubsetPrior P Qb p) = 1 ∧
--             (∑ p : P, primeSubsetPrior P Qd p) = 1 ∧
--             (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
--               (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) ∧
--             ∃ cb ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊,
--             ∃ cd ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊,
--               Real.exp (-(Real.log 2 + 2) * m) ≤
--                 ∑ x ∈ balancedTupleSet (m / 2) (fun _ (p : P) => good p),
--                   productPrior (fun _ => primeSubsetPrior P Qb) x *
--                     initialLogSumWeight (fun p : P => (p : ℕ)) cb x ∧
--               Real.exp (-(Real.log 2 + 2) * m) ≤
--                 ∑ x ∈ balancedTupleSet (m / 2) (fun _ (p : P) => good p),
--                   productPrior (fun _ => primeSubsetPrior P Qd) x *
--                     initialLogSumWeight (fun p : P => (p : ℕ)) cd x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.PublishedBonamiBound`, `OAI.Ostmann.PublishedQuadraticLargeSieve`, `OAI.Ostmann.PublishedSummandSizeBound`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.residueDensity`, `OAI.Ostmann.tailDensityMask` and `OAI.Ostmann.tailResidues` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.balancedTupleSet`, `OAI.Ostmann.negTailResidues`, `OAI.Ostmann.productPrior` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput`, `OAI.Ostmann.PublishedRealZeroInput` and `OAI.Ostmann.PublishedSiegelBound` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.initialLogSumWeight` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.tailCharacterBias` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.EventuallyPrimeSumset` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proof of `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/TailInitialBroadPriors.lean (declaration OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers)

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.initial_broad_prior_centers
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (k cutoff : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      let m := spectatorBulkCount k L
      let good := fun p : ℕ => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3
      ∃ Qd : Finset ℕ,
        Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
        (∀ p ∈ Qd, cutoff ≤ p ∧ good p ∧ tailCharacterBias A N p ≤ ε / 2) ∧
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → Qb ⊆ P → Qd ⊆ P →
          (∑ p : P, primeSubsetPrior P Qb p) = 1 ∧
          (∑ p : P, primeSubsetPrior P Qd p) = 1 ∧
          (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
            (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) ∧
          ∃ cb ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊,
          ∃ cd ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊,
            Real.exp (-(Real.log 2 + 2) * m) ≤
              ∑ x ∈ balancedTupleSet (m / 2) (fun _ (p : P) => good p),
                productPrior (fun _ => primeSubsetPrior P Qb) x *
                  initialLogSumWeight (fun p : P => (p : ℕ)) cb x ∧
            Real.exp (-(Real.log 2 + 2) * m) ≤
              ∑ x ∈ balancedTupleSet (m / 2) (fun _ (p : P) => good p),
                productPrior (fun _ => primeSubsetPrior P Qd) x *
                  initialLogSumWeight (fun p : P => (p : ℕ)) cd x := by
  sorry

end Ostmann

end OAI
end
