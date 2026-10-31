-- Prove2me | Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_constructed_initial_amplitude
-- name    : OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:17:31.233398+00:00
-- url     : https://prove2.me/theorems/31528f1a-1b52-44a6-8ebc-bf2887a4451b
-- title:
--   OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude` of [lean/OAI/NumberTheory/Ostmann/Construction/ConstructedInitialAmplitude.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstructedInitialAmplitude.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators SchwartzMap FourierTransform`):
--
--   ```lean
--   theorem EventuallyPrimeSumset.constructed_initial_amplitude
--       (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
--       (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
--       (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
--       (sieve : PublishedQuadraticLargeSieve) {A B : Set ℕ}
--       (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
--       (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
--       (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
--       (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
--       (hPNT : PublishedSmoothPrincipalPNT)
--       (ψ : 𝓢(ℝ, ℂ)) (H c : ℝ) (hH : 0 ≤ H) (hc : 0 < c)
--       (hψ : ∀ x, 0 ≤ (ψ x).re) (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
--       (hψlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ t).re) :
--       ∃ N : ℕ, ∃ a : ℝ, 0 < a ∧
--         (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
--         ∀ k : ℕ, 2 ≤ k → ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
--         2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
--           (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1 →
--         14 * (64 * tailCellLinearRate a CM + 3) ≤ (k : ℝ) ^ 3 →
--         ∀ cutoff : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ reference : ℕ in atTop,
--         let L := Real.log (Real.log (reference : ℝ))
--         ∃ lo : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo ∧ lo ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
--         ∃ F : Finset ℕ, F ⊆ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
--           (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2) ∧
--         ∃ Y : ℝ, ∃ hi : ℕ, (hi : ℝ) = Real.exp Y ∧
--           2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y ∧
--           Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 ∧
--           Real.exp ((4 / 100 : ℝ) * L) ≤ Y ∧ Y ≤ Real.exp L ∧
--         ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
--           Real.exp (-(91 / 100 : ℝ) * L) ≤
--             smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
--           smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L ∧
--         ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
--         ∃ Qd : Finset ℕ, ∃ cb cd : ℤ, ∃ top : ℕ, ∃ centers : List ℕ,
--           Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
--             (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
--           L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
--           (∀ p ∈ Qd, cutoff ≤ p ∧
--             ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
--               residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧ tailCharacterBias A N p ≤ ε / 2) ∧
--           cb ∈ Finset.Icc (0 : ℤ)
--             ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ ∧
--           cd ∈ Finset.Icc (0 : ℤ)
--             ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ ∧
--           SelectedSmallTailCell A B N a CM L Y hi D
--             ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top ∧
--           List.Forall₂ (fun j w => SelectedSmallTailCell A B N a CM L Y hi D (w / 4) j)
--             centers (movingCompensationTargets
--               (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
--               (movingCompensationGaps k BD Bz L)) ∧ centers.length = k ∧
--           let P := Nat.primesLE (tailCollisionCutoff Y)
--           let _ : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(Nat.prime_of_mem_primesLE p.property).ne_zero⟩
--           let m := spectatorBulkCount k L
--           let cells := initialSmallCellList top centers
--           let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
--             (Real.exp ((6 / 1000 : ℝ) * L)) \ D
--           let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd (m / 2) (m / 2) top centers
--           let w := initialHalfCutoffWeight (fun p : P => (p : ℕ)) (m / 2) (m / 2) cells.length cb cd
--           let Δ := selectedInitialLogCenter G Y cb cd top centers
--           let width : ℝ := 2 * (cells.length + 3)
--           ∀ T : ℕ → ℝ,
--           let V := movingProductNaturalCutoff T (Y + Δ + width) Y ((m : ℝ) / 4) 0
--           let Ftest : Fin ((m / 2 + (m / 2 + cells.length)) + 1) →
--             (p : P) → ZMod (p : ℕ) → ℂ :=
--               primeHalfTests P (fun p => tailDensityMask A N p) (fun p => decide ((p : ℕ) ∈ F))
--           Real.exp (-(6 * Real.log 2 + 13) * m) ≤
--             ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append Ftest Ftest) ψ (Real.exp Y) V
--               (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ)))‖ ∧
--           ∃ sl sr : Fin (m / 2) → P, Function.Injective (Fin.append sl sr) ∧
--             (∀ i, (sl i : ℕ) ∈ Qd) ∧ (∀ i, (sr i : ℕ) ∈ Qd) ∧
--             Real.exp (-(6 * Real.log 2 + 13) * m) ≤
--               ‖initialFrozenAmplitude P (m / 2) (m / 2) cells.length
--                 (smoothGiantPrior P logCellProfile G) (fun _ => primeSubsetPrior P Qb)
--                 (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D (cells.get i)))
--                 (Fin.append Ftest Ftest) ψ (Real.exp Y) V
--                 (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ))) sl sr‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.ComplexZeroEnumeration` and `OAI.Ostmann.PrimitiveComplexCharacter` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.MertensHarmonicEstimate`, `OAI.Ostmann.PublishedAdditiveLargeSieve`, `OAI.Ostmann.PublishedBonamiBound`, `OAI.Ostmann.PublishedQuadraticLargeSieve`, `OAI.Ostmann.PublishedSmoothPrincipalPNT`, `OAI.Ostmann.PublishedSummandSizeBound`, `OAI.Ostmann.SelectedSmallTailCell`, `OAI.Ostmann.logCellProfile`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.residueDensity`, `OAI.Ostmann.selectedTailCellPrimes`, `OAI.Ostmann.tailCollisionCutoff`, `OAI.Ostmann.tailDensityMask`, `OAI.Ostmann.tailResidues` and `OAI.Ostmann.tailSupport` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.doubledHalfWeight`, `OAI.Ostmann.favorableTransformPrimes`, `OAI.Ostmann.initialSmallCellList`, `OAI.Ostmann.logLogPrimeBand`, `OAI.Ostmann.movingCompensationGaps`, `OAI.Ostmann.movingCompensationTargets`, `OAI.Ostmann.movingInitialGapTotal`, `OAI.Ostmann.movingProductNaturalCutoff`, `OAI.Ostmann.movingProtectedTarget`, `OAI.Ostmann.negTailResidues`, `OAI.Ostmann.selectedInitialLogCenter`, `OAI.Ostmann.smoothGiantLogNormalizer`, `OAI.Ostmann.smoothGiantMass`, `OAI.Ostmann.smoothGiantPrimeRange`, `OAI.Ostmann.smoothGiantPrior`, `OAI.Ostmann.spectatorBulkCount` and `OAI.Ostmann.tailCellLinearRate` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedComplexZeroDensity`, `OAI.Ostmann.PublishedComplexZeroRegion`, `OAI.Ostmann.PublishedProgressionInput`, `OAI.Ostmann.PublishedRealZeroInput`, `OAI.Ostmann.PublishedSiegelBound` and `OAI.Ostmann.PublishedSmoothExplicitFormula` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.initialFrozenAmplitude` and `OAI.Ostmann.initialHalfCutoffWeight` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.selectedInitialHalfPrior` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.primeHalfTests`, `OAI.Ostmann.regularInitialAmplitude`, `OAI.Ostmann.tailCharacterBias` and `OAI.Ostmann.tailFourierMass` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.EventuallyPrimeSumset` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proof of `OAI.Ostmann.twoInfiniteSummandsImpossible_of_published` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstructedInitialAmplitude.lean (declaration OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude)

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
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem EventuallyPrimeSumset.constructed_initial_amplitude
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT)
    (ψ : 𝓢(ℝ, ℂ)) (H c : ℝ) (hH : 0 ≤ H) (hc : 0 < c)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (hψlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ t).re) :
    ∃ N : ℕ, ∃ a : ℝ, 0 < a ∧
      (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      ∀ k : ℕ, 2 ≤ k → ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
      2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
        (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1 →
      14 * (64 * tailCellLinearRate a CM + 3) ≤ (k : ℝ) ^ 3 →
      ∀ cutoff : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ reference : ℕ in atTop,
      let L := Real.log (Real.log (reference : ℝ))
      ∃ lo : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo ∧ lo ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
      ∃ F : Finset ℕ, F ⊆ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
        (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2) ∧
      ∃ Y : ℝ, ∃ hi : ℕ, (hi : ℝ) = Real.exp Y ∧
        2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y ∧
        Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 ∧
        Real.exp ((4 / 100 : ℝ) * L) ≤ Y ∧ Y ≤ Real.exp L ∧
      ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
        Real.exp (-(91 / 100 : ℝ) * L) ≤
          smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
        smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L ∧
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ Qd : Finset ℕ, ∃ cb cd : ℤ, ∃ top : ℕ, ∃ centers : List ℕ,
        Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
        (∀ p ∈ Qd, cutoff ≤ p ∧
          ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
            residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧ tailCharacterBias A N p ≤ ε / 2) ∧
        cb ∈ Finset.Icc (0 : ℤ)
          ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ ∧
        cd ∈ Finset.Icc (0 : ℤ)
          ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ ∧
        SelectedSmallTailCell A B N a CM L Y hi D
          ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a CM L Y hi D (w / 4) j)
          centers (movingCompensationTargets
            (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
            (movingCompensationGaps k BD Bz L)) ∧ centers.length = k ∧
        let P := Nat.primesLE (tailCollisionCutoff Y)
        let _ : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(Nat.prime_of_mem_primesLE p.property).ne_zero⟩
        let m := spectatorBulkCount k L
        let cells := initialSmallCellList top centers
        let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
          (Real.exp ((6 / 1000 : ℝ) * L)) \ D
        let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd (m / 2) (m / 2) top centers
        let w := initialHalfCutoffWeight (fun p : P => (p : ℕ)) (m / 2) (m / 2) cells.length cb cd
        let Δ := selectedInitialLogCenter G Y cb cd top centers
        let width : ℝ := 2 * (cells.length + 3)
        ∀ T : ℕ → ℝ,
        let V := movingProductNaturalCutoff T (Y + Δ + width) Y ((m : ℝ) / 4) 0
        let Ftest : Fin ((m / 2 + (m / 2 + cells.length)) + 1) →
          (p : P) → ZMod (p : ℕ) → ℂ :=
            primeHalfTests P (fun p => tailDensityMask A N p) (fun p => decide ((p : ℕ) ∈ F))
        Real.exp (-(6 * Real.log 2 + 13) * m) ≤
          ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append Ftest Ftest) ψ (Real.exp Y) V
            (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ)))‖ ∧
        ∃ sl sr : Fin (m / 2) → P, Function.Injective (Fin.append sl sr) ∧
          (∀ i, (sl i : ℕ) ∈ Qd) ∧ (∀ i, (sr i : ℕ) ∈ Qd) ∧
          Real.exp (-(6 * Real.log 2 + 13) * m) ≤
            ‖initialFrozenAmplitude P (m / 2) (m / 2) cells.length
              (smoothGiantPrior P logCellProfile G) (fun _ => primeSubsetPrior P Qb)
              (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D (cells.get i)))
              (Fin.append Ftest Ftest) ψ (Real.exp Y) V
              (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ))) sl sr‖ := by
  sorry

end Ostmann

end OAI
end
