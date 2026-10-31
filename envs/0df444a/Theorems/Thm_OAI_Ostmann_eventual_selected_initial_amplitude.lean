-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_selected_initial_amplitude
-- name    : OAI.Ostmann.eventual_selected_initial_amplitude
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:24:55.847874+00:00
-- url     : https://prove2.me/theorems/cc7776fc-56a6-4cbe-83e9-9c6e059419fd
-- title:
--   OAI.Ostmann.eventual_selected_initial_amplitude: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_selected_initial_amplitude` of [lean/OAI/NumberTheory/Ostmann/Construction/SelectedInitialAmplitude.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedInitialAmplitude.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators SchwartzMap FourierTransform`):
--
--   ```lean
--   theorem eventual_selected_initial_amplitude
--       (k : ℕ) (hk : 2 ≤ k) (Bs BD Bz a C atail c δ H : ℝ)
--       (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hatail : 0 < atail) (hc : 0 < c) (hδ : 0 < δ)
--       (hgap : 2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
--         (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1)
--       (hklarge : 14 * (64 * tailCellLinearRate a C + 3) ≤ (k : ℝ) ^ 3)
--       (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re)
--       (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0) :
--       ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ}
--         {Y G cb cd : ℝ} {D Qb Qd : Finset ℕ} {centers : List ℕ},
--         0 < Y → Y ≤ Real.exp L →
--         SelectedSmallTailCell A B N a C L Y hi D
--           ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
--         List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
--           centers (movingCompensationTargets
--             (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
--             (movingCompensationGaps k BD Bz L)) → centers.length = k →
--         ∀ (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)], (∀ p ∈ P, p.Prime) →
--         initialRegularPrimeRange L ⊆ P → smoothGiantPrimeRange G ⊆ P →
--         0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G →
--         smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L →
--         (∑ p : P, primeSubsetPrior P Qb p) = 1 →
--         (∑ p : P, primeSubsetPrior P Qd p) = 1 →
--         (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
--           (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) →
--         let m := spectatorBulkCount k L
--         let cells := initialSmallCellList top centers
--         let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd (m / 2) (m / 2) top centers
--         let w := initialHalfCutoffWeight (fun p : P => (p : ℕ)) (m / 2) (m / 2) cells.length cb cd
--         let good := fun p : P => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
--           residueDensity (tailDensityMask A N p) ≤ 2 / 3
--         Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
--           ∑ x ∈ balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ p => good p),
--             productPrior (Fin.tail ν) x * w x →
--         (∀ i (p : P), ν i p ≠ 0 → Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ (p : ℝ)) →
--         (∑ p : P, (p : ℝ)⁻¹) ≤ 2 * m →
--         ∀ (E : Finset ℤ) (favorable : P → Bool),
--         atail * Real.sqrt (Real.exp Y) / Y ^ 3 ≤ (E.card : ℝ) →
--         (∀ e ∈ E, c ≤ (ψ ((e : ℝ) / Real.exp Y)).re) →
--         (∀ e ∈ E, ∀ p : P, (e : ZMod (p : ℕ)) ∈ tailDensityMask A N p) →
--         (E.card : ℝ) * δ ≤ ∑ e ∈ E,
--           (∑ p : P, (smoothGiantPrior P logCellProfile G p : ℂ) *
--             primePhysicalTest (tailDensityMask A N p) true (favorable p)
--               (e : ZMod (p : ℕ))).re →
--         ∀ T : ℕ → ℝ,
--         let Δ := selectedInitialLogCenter G Y cb cd top centers
--         let width : ℝ := 2 * (cells.length + 3)
--         let V := movingProductNaturalCutoff T (Y + Δ + width) Y ((m : ℝ) / 4) 0
--         let F : Fin ((m / 2 + (m / 2 + cells.length)) + 1) →
--           (p : P) → ZMod (p : ℕ) → ℂ := primeHalfTests P (fun p => tailDensityMask A N p) favorable
--         Real.exp (-(6 * Real.log 2 + 13) * m) ≤
--           ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append F F) ψ (Real.exp Y) V
--             (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ)))‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.SelectedSmallTailCell`, `OAI.Ostmann.logCellProfile`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.residueDensity` and `OAI.Ostmann.tailDensityMask` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.balancedTupleSet`, `OAI.Ostmann.doubledHalfWeight`, `OAI.Ostmann.initialRegularPrimeRange`, `OAI.Ostmann.initialSmallCellList`, `OAI.Ostmann.movingCompensationGaps`, `OAI.Ostmann.movingCompensationTargets`, `OAI.Ostmann.movingInitialGapTotal`, `OAI.Ostmann.movingProductNaturalCutoff`, `OAI.Ostmann.movingProtectedTarget`, `OAI.Ostmann.productPrior`, `OAI.Ostmann.selectedInitialLogCenter`, `OAI.Ostmann.smoothGiantLogNormalizer`, `OAI.Ostmann.smoothGiantMass`, `OAI.Ostmann.smoothGiantPrimeRange`, `OAI.Ostmann.smoothGiantPrior`, `OAI.Ostmann.spectatorBulkCount` and `OAI.Ostmann.tailCellLinearRate` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.initialHalfCutoffWeight` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.selectedInitialHalfPrior` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.primeHalfTests`, `OAI.Ostmann.primePhysicalTest` and `OAI.Ostmann.regularInitialAmplitude` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedInitialAmplitude.lean (declaration OAI.Ostmann.eventual_selected_initial_amplitude)

import Mathlib
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

theorem eventual_selected_initial_amplitude
    (k : ℕ) (hk : 2 ≤ k) (Bs BD Bz a C atail c δ H : ℝ)
    (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hatail : 0 < atail) (hc : 0 < c) (hδ : 0 < δ)
    (hgap : 2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
      (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1)
    (hklarge : 14 * (64 * tailCellLinearRate a C + 3) ≤ (k : ℝ) ^ 3)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ}
      {Y G cb cd : ℝ} {D Qb Qd : Finset ℕ} {centers : List ℕ},
      0 < Y → Y ≤ Real.exp L →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        centers (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) → centers.length = k →
      ∀ (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)], (∀ p ∈ P, p.Prime) →
      initialRegularPrimeRange L ⊆ P → smoothGiantPrimeRange G ⊆ P →
      0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G →
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L →
      (∑ p : P, primeSubsetPrior P Qb p) = 1 →
      (∑ p : P, primeSubsetPrior P Qd p) = 1 →
      (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
        (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) →
      let m := spectatorBulkCount k L
      let cells := initialSmallCellList top centers
      let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd (m / 2) (m / 2) top centers
      let w := initialHalfCutoffWeight (fun p : P => (p : ℕ)) (m / 2) (m / 2) cells.length cb cd
      let good := fun p : P => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3
      Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
        ∑ x ∈ balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ p => good p),
          productPrior (Fin.tail ν) x * w x →
      (∀ i (p : P), ν i p ≠ 0 → Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ (p : ℝ)) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ 2 * m →
      ∀ (E : Finset ℤ) (favorable : P → Bool),
      atail * Real.sqrt (Real.exp Y) / Y ^ 3 ≤ (E.card : ℝ) →
      (∀ e ∈ E, c ≤ (ψ ((e : ℝ) / Real.exp Y)).re) →
      (∀ e ∈ E, ∀ p : P, (e : ZMod (p : ℕ)) ∈ tailDensityMask A N p) →
      (E.card : ℝ) * δ ≤ ∑ e ∈ E,
        (∑ p : P, (smoothGiantPrior P logCellProfile G p : ℂ) *
          primePhysicalTest (tailDensityMask A N p) true (favorable p)
            (e : ZMod (p : ℕ))).re →
      ∀ T : ℕ → ℝ,
      let Δ := selectedInitialLogCenter G Y cb cd top centers
      let width : ℝ := 2 * (cells.length + 3)
      let V := movingProductNaturalCutoff T (Y + Δ + width) Y ((m : ℝ) / 4) 0
      let F : Fin ((m / 2 + (m / 2 + cells.length)) + 1) →
        (p : P) → ZMod (p : ℕ) → ℂ := primeHalfTests P (fun p => tailDensityMask A N p) favorable
      Real.exp (-(6 * Real.log 2 + 13) * m) ≤
        ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append F F) ψ (Real.exp Y) V
          (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ)))‖ := by
  sorry

end Ostmann

end OAI
end
