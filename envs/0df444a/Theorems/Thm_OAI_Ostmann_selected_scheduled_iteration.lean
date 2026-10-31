-- Prove2me | Theorems.Thm_OAI_Ostmann_selected_scheduled_iteration
-- name    : OAI.Ostmann.selected_scheduled_iteration
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:33:14.872249+00:00
-- url     : https://prove2.me/theorems/d1e553de-0b46-46ee-be3c-2cbf6f85aa1b
-- title:
--   OAI.Ostmann.selected_scheduled_iteration: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.selected_scheduled_iteration` of [lean/OAI/NumberTheory/Ostmann/Construction/SelectedScheduledIteration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedScheduledIteration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem selected_scheduled_iteration
--       {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
--       {N hi top : ℕ} {a C L Y G cb cd Dlog Bs BD Bz : ℝ}
--       {D P Qb : Finset ℕ} {cs : List ℕ} (k : ℕ) (hk : 2 ≤ k)
--       (hP : ∀ p ∈ P, p.Prime) (hambient : initialRegularPrimeRange L ⊆ P)
--       (hL : 1 ≤ L) (hY : 0 < Y) (hYupper : Y ≤ Real.exp L)
--       (hcell : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
--       (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
--       (hm : 256 ≤ (spectatorBulkCount k L : ℝ))
--       (hG : 1 ≤ G) (hcb : 0 ≤ cb) (hD : |Dlog - 2 * cd| ≤ 2)
--       (hBs : 0 ≤ Bs) (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
--       (herror : 256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
--       (hbudget : 40 * (2 * ((initialSmallCellList top cs).length + 3) + 14 + 4 * cs.length) +
--         20 * Real.log 2 < (spectatorBulkCount k L : ℝ))
--       (htop : SelectedSmallTailCell A B N a C L Y hi D
--         ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
--       (hcs : List.Forall₂
--         (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
--         cs (movingCompensationTargets
--           (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
--           (movingCompensationGaps k BD Bz L)))
--       (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
--       (hbulk : Qb ⊆ initialRegularPrimeRange L)
--       (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
--       (hdis : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
--       (b d : ℕ)
--       (sl sr : Fin d → P) (fallback : P)
--       {J : Type} (q : J → ℕ) [∀ i, Fact (q i).Prime]
--       (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
--       (ψ : 𝓢(ℝ, ℂ)) (X lo upper : ℝ) (hX : 0 < X)
--       (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
--       (hpos : 0 < smoothGiantMass (smoothGiantPrimeRange G) φ G)
--       (outside : List ℕ) (favorable : ℕ → Bool) (B₀ : ℝ) :
--       let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
--       let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
--       let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
--       let V := movingProductNaturalCutoff T W (Y - Dlog) ((spectatorBulkCount k L : ℝ) / 4)
--       let μ := completedCompensationPrior A B N Y hi D P top cs
--       let cell := fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D c)
--       let F := movingOriginalLeaf Subtype.val q
--         (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
--         g Dq S ψ X lo upper
--       let I := Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊
--       let ρ := smoothGiantPrior (smoothGiantPrimeRange G) φ G
--       let greg := normalizedResidueFamily (tailDensityMask A N)
--       let η := fun n => scheduledCellAmplitude Subtype.val outside μ (scheduledChildBound V)
--         (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) ρ
--         cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable
--       let diag := fun n => scheduledCellDiagonal Subtype.val outside μ (scheduledChildBound V)
--         (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) I ρ
--         cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable
--       X * upper ≤ Real.exp W →
--       (∀ n ≤ k, (V n : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L))) →
--       (∀ n ≤ k, (V n : ℝ) < Real.exp (G - 1)) →
--       smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G ≤ L →
--       Real.exp (-B₀ * (spectatorBulkCount k L : ℝ)) ≤ ‖η 0‖ →
--       (∀ n < k, diag n ≤ Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ n * spectatorBulkCount k L)) →
--       ∀ n ≤ k, Real.exp (-(B₀ + 1) * (2 : ℝ) ^ n * spectatorBulkCount k L) ≤ ‖η n‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MovingSlotState`, `OAI.Ostmann.SelectedSmallTailCell`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.selectedTailCellPrimes`, `OAI.Ostmann.tailDefectBudget`, `OAI.Ostmann.tailDensityMask` and `OAI.Ostmann.tailResidues` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.initialRegularPrimeRange`, `OAI.Ostmann.initialSmallCellList`, `OAI.Ostmann.movingCellPivotExponent`, `OAI.Ostmann.movingCompensationGaps`, `OAI.Ostmann.movingCompensationTargets`, `OAI.Ostmann.movingInitialGapTotal`, `OAI.Ostmann.movingProductNaturalCutoff`, `OAI.Ostmann.movingProtectedTarget`, `OAI.Ostmann.negTailResidues`, `OAI.Ostmann.scheduledChildBound`, `OAI.Ostmann.scheduledPivotCaps`, `OAI.Ostmann.selectedCompensationCenter`, `OAI.Ostmann.selectedInitialLogCenter`, `OAI.Ostmann.smoothGiantLogNormalizer`, `OAI.Ostmann.smoothGiantMass`, `OAI.Ostmann.smoothGiantPrimeRange`, `OAI.Ostmann.smoothGiantPrior`, `OAI.Ostmann.spectatorBulkCount` and `OAI.Ostmann.tailCellLinearRate` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.completedCompensationPrior` and `OAI.Ostmann.initialMovingDataCutoff` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.normalizedResidueFamily`, `OAI.Ostmann.scheduledCellAmplitude` and `OAI.Ostmann.scheduledCellDiagonal` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalLeaf` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.twoInfiniteSummandsImpossible_of_published` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedScheduledIteration.lean (declaration OAI.Ostmann.selected_scheduled_iteration)

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
open scoped Classical BigOperators SchwartzMap

theorem selected_scheduled_iteration
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    {N hi top : ℕ} {a C L Y G cb cd Dlog Bs BD Bz : ℝ}
    {D P Qb : Finset ℕ} {cs : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hP : ∀ p ∈ P, p.Prime) (hambient : initialRegularPrimeRange L ⊆ P)
    (hL : 1 ≤ L) (hY : 0 < Y) (hYupper : Y ≤ Real.exp L)
    (hcell : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hm : 256 ≤ (spectatorBulkCount k L : ℝ))
    (hG : 1 ≤ G) (hcb : 0 ≤ cb) (hD : |Dlog - 2 * cd| ≤ 2)
    (hBs : 0 ≤ Bs) (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (herror : 256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hbudget : 40 * (2 * ((initialSmallCellList top cs).length + 3) + 14 + 4 * cs.length) +
      20 * Real.log 2 < (spectatorBulkCount k L : ℝ))
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L)))
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (hdis : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (b d : ℕ)
    (sl sr : Fin d → P) (fallback : P)
    {J : Type} (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : 𝓢(ℝ, ℂ)) (X lo upper : ℝ) (hX : 0 < X)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hpos : 0 < smoothGiantMass (smoothGiantPrimeRange G) φ G)
    (outside : List ℕ) (favorable : ℕ → Bool) (B₀ : ℝ) :
    let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    let V := movingProductNaturalCutoff T W (Y - Dlog) ((spectatorBulkCount k L : ℝ) / 4)
    let μ := completedCompensationPrior A B N Y hi D P top cs
    let cell := fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D c)
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
      g Dq S ψ X lo upper
    let I := Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊
    let ρ := smoothGiantPrior (smoothGiantPrimeRange G) φ G
    let greg := normalizedResidueFamily (tailDensityMask A N)
    let η := fun n => scheduledCellAmplitude Subtype.val outside μ (scheduledChildBound V)
      (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) ρ
      cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable
    let diag := fun n => scheduledCellDiagonal Subtype.val outside μ (scheduledChildBound V)
      (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) I ρ
      cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable
    X * upper ≤ Real.exp W →
    (∀ n ≤ k, (V n : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L))) →
    (∀ n ≤ k, (V n : ℝ) < Real.exp (G - 1)) →
    smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G ≤ L →
    Real.exp (-B₀ * (spectatorBulkCount k L : ℝ)) ≤ ‖η 0‖ →
    (∀ n < k, diag n ≤ Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ n * spectatorBulkCount k L)) →
    ∀ n ≤ k, Real.exp (-(B₀ + 1) * (2 : ℝ) ^ n * spectatorBulkCount k L) ≤ ‖η n‖ := by
  sorry

end Ostmann

end OAI
end
