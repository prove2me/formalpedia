-- Prove2me | Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_constructed_initial_nongiant_priors
-- name    : OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:16:59.622849+00:00
-- url     : https://prove2.me/theorems/db4b39cd-b920-49b8-bde3-ad84b7dd5ea5
-- title:
--   OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors` of [lean/OAI/NumberTheory/Ostmann/Construction/ConstructedInitialNongiantPriors.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstructedInitialNongiantPriors.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem EventuallyPrimeSumset.constructed_initial_nongiant_priors
--       (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
--       (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
--       (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
--       {C : ℝ} (hM : MertensEstimate C)
--       {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
--       (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) :
--       ∃ a : ℝ, 0 < a ∧ ∀ k : ℕ, 2 ≤ k →
--         ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
--         ∀ cutoff : ℕ, ∀ ε : ℝ, 0 < ε →
--         ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
--         Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
--         ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
--         ∀ lo G : ℝ,
--         2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
--         Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
--         lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
--         ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
--         ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → initialRegularPrimeRange L ⊆ P →
--         let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
--           (Real.exp ((6 / 1000 : ℝ) * L)) \ D
--         let m := spectatorBulkCount k L
--         ∃ Qd : Finset ℕ, ∃ cb cd : ℤ, ∃ top : ℕ, ∃ centers : List ℕ,
--           Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
--             (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
--           L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
--           (∀ p ∈ Qd, cutoff ≤ p ∧
--             ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
--               residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧
--             tailCharacterBias A N p ≤ ε / 2) ∧
--           cb ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ ∧
--           cd ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ ∧
--           SelectedSmallTailCell A B N a C L Y hi D
--             ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top ∧
--           List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
--             centers (movingCompensationTargets
--               (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
--               (movingCompensationGaps k BD Bz L)) ∧
--           centers.length = k ∧
--           |2 * (G + cb + cd + 3 * top + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) -
--             (Y + spectatorBaseGap Bs ((k : ℝ) ^ 4) m)| ≤
--               (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) ∧
--           (∑ p : P, primeSubsetPrior P Qb p) = 1 ∧
--           (∑ p : P, primeSubsetPrior P Qd p) = 1 ∧
--           (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
--             (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) ∧
--           let cells := initialSmallCellList top centers
--           let μc := fun i : Fin cells.length => primeSubsetPrior P
--             (selectedTailCellPrimes A B N Y hi D (cells.get i))
--           Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
--             ∑ x ∈ balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ (p : P) =>
--               (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
--                 residueDensity (tailDensityMask A N p) ≤ 2 / 3),
--               productPrior (Fin.append (fun _ : Fin (m / 2) => primeSubsetPrior P Qb)
--                 (Fin.append (fun _ : Fin (m / 2) => primeSubsetPrior P Qd) μc)) x *
--                   initialLogSumWeight (fun p : P => (p : ℕ)) cb
--                     (fun i => x (i.castAdd (m / 2 + cells.length))) *
--                   initialLogSumWeight (fun p : P => (p : ℕ)) cd
--                     (fun i => x ((i.castAdd cells.length).natAdd (m / 2)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.PublishedBonamiBound`, `OAI.Ostmann.PublishedQuadraticLargeSieve`, `OAI.Ostmann.PublishedSummandSizeBound`, `OAI.Ostmann.SelectedSmallTailCell`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.residueDensity`, `OAI.Ostmann.selectedTailCellPrimes`, `OAI.Ostmann.tailDefectBudget`, `OAI.Ostmann.tailDensityMask` and `OAI.Ostmann.tailResidues` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.balancedTupleSet`, `OAI.Ostmann.initialRegularPrimeRange`, `OAI.Ostmann.initialSmallCellList`, `OAI.Ostmann.movingCompensationGaps`, `OAI.Ostmann.movingCompensationTargets`, `OAI.Ostmann.movingInitialGapTotal`, `OAI.Ostmann.movingProtectedTarget`, `OAI.Ostmann.negTailResidues`, `OAI.Ostmann.productPrior`, `OAI.Ostmann.spectatorBaseGap` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput`, `OAI.Ostmann.PublishedRealZeroInput` and `OAI.Ostmann.PublishedSiegelBound` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.initialLogSumWeight` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.tailCharacterBias` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.EventuallyPrimeSumset` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proof of `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstructedInitialNongiantPriors.lean (declaration OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors)

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

theorem EventuallyPrimeSumset.constructed_initial_nongiant_priors
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    ∃ a : ℝ, 0 < a ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
      ∀ cutoff : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ lo G : ℝ,
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → initialRegularPrimeRange L ⊆ P →
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      let m := spectatorBulkCount k L
      ∃ Qd : Finset ℕ, ∃ cb cd : ℤ, ∃ top : ℕ, ∃ centers : List ℕ,
        Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
        (∀ p ∈ Qd, cutoff ≤ p ∧
          ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
            residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧
          tailCharacterBias A N p ≤ ε / 2) ∧
        cb ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ ∧
        cd ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ ∧
        SelectedSmallTailCell A B N a C L Y hi D
          ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
          centers (movingCompensationTargets
            (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
            (movingCompensationGaps k BD Bz L)) ∧
        centers.length = k ∧
        |2 * (G + cb + cd + 3 * top + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) -
          (Y + spectatorBaseGap Bs ((k : ℝ) ^ 4) m)| ≤
            (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) ∧
        (∑ p : P, primeSubsetPrior P Qb p) = 1 ∧
        (∑ p : P, primeSubsetPrior P Qd p) = 1 ∧
        (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
          (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) ∧
        let cells := initialSmallCellList top centers
        let μc := fun i : Fin cells.length => primeSubsetPrior P
          (selectedTailCellPrimes A B N Y hi D (cells.get i))
        Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
          ∑ x ∈ balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ (p : P) =>
            (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
              residueDensity (tailDensityMask A N p) ≤ 2 / 3),
            productPrior (Fin.append (fun _ : Fin (m / 2) => primeSubsetPrior P Qb)
              (Fin.append (fun _ : Fin (m / 2) => primeSubsetPrior P Qd) μc)) x *
                initialLogSumWeight (fun p : P => (p : ℕ)) cb
                  (fun i => x (i.castAdd (m / 2 + cells.length))) *
                initialLogSumWeight (fun p : P => (p : ℕ)) cd
                  (fun i => x ((i.castAdd cells.length).natAdd (m / 2))) := by
  sorry

end Ostmann

end OAI
end
