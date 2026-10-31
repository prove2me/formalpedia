-- Prove2me | Theorems.Thm_OAI_Ostmann_frozen_initial_small_amplitude
-- name    : OAI.Ostmann.frozen_initial_small_amplitude
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:32:18.608341+00:00
-- url     : https://prove2.me/theorems/ec19f736-d46d-460b-83a5-2a0009068af7
-- title:
--   OAI.Ostmann.frozen_initial_small_amplitude: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.frozen_initial_small_amplitude` of [lean/OAI/NumberTheory/Ostmann/Construction/FrozenInitialSmallAmplitude.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/FrozenInitialSmallAmplitude.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical BigOperators SchwartzMap FourierTransform`):
--
--   ```lean
--   theorem frozen_initial_small_amplitude
--       {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
--       {D Qd : Finset ℕ} {cs : List ℕ} {targets : List ℝ}
--       (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
--       (hcs : List.Forall₂
--         (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) cs targets)
--       (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)] (hP : ∀ p ∈ P, p.Prime)
--       (hQP : initialRegularPrimeRange L ⊆ P)
--       (hgiant : smoothGiantPrimeRange G ⊆ P)
--       (bulk : Finset ℕ) (hbulk : bulk ⊆ initialRegularPrimeRange L)
--       (b d : ℕ) (sl sr : Fin d → initialRegularPrimeRange L)
--       (hinj : Function.Injective (Fin.append
--         (primeAlphabetEmbedding hQP ∘ sl) (primeAlphabetEmbedding hQP ∘ sr)))
--       (hsl : ∀ i, (sl i : ℕ) ∈ Qd) (hsr : ∀ i, (sr i : ℕ) ∈ Qd)
--       (fallback : initialRegularPrimeRange L)
--       (sets : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool) (ψ : 𝓢(ℝ, ℂ))
--       (Qμ : ℕ → Finset ℕ) (childBound pivotBound V : ℕ → ℕ)
--       (hV0 : (V 0 : ℝ) < Real.exp (G - 1)) :
--       let Q := initialRegularPrimeRange L
--       let e := primeAlphabetEmbedding hQP
--       let cells := initialSmallCellList top cs
--       let q : Fin (d + d) → ℕ := fun i => ((Fin.append (e ∘ sl) (e ∘ sr) i : P) : ℕ)
--       let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
--         (Nat.coprime_primes (hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property)
--           (hP _ (Fin.append (e ∘ sl) (e ∘ sr) j).property)).mpr
--             (fun h => hij (hinj (Subtype.ext h)))
--       let _ : ∀ i, Fact (q i).Prime := fun i =>
--         ⟨hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property⟩
--       let Δ := selectedInitialLogCenter G Y cb cd top cs
--       let F := movingOriginalLeaf Subtype.val q
--         (initialMovingDataCutoff Subtype.val b d cells.length cb cd sl sr fallback)
--         (fun i => normalizedResidueFamily sets (q i)) (initialSpectatorCofactor q hc) Finset.univ
--         (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ))
--         (Real.exp (Δ - 2 * (cells.length + 3))) (Real.exp (Δ + 2 * (cells.length + 3)))
--       initialFrozenAmplitude P b d cells.length (smoothGiantPrior P logCellProfile G)
--         (fun _ => primeSubsetPrior P bulk)
--         (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y endpoint D (cells.get i)))
--         (Fin.append (primeHalfTests (n := b + (d + cells.length)) P (fun p => sets p) (fun p => fav p))
--           (primeHalfTests (n := b + (d + cells.length)) P (fun p => sets p) (fun p => fav p)))
--         ψ (Real.exp Y) (V 0)
--         (doubledHalfWeight (fun x : Fin (b + (d + cells.length) + 1) → P =>
--           (initialHalfCutoffWeight Subtype.val b d cells.length cb cd (Fin.tail x) : ℂ)))
--         (e ∘ sl) (e ∘ sr) =
--       scheduledCellAmplitude Subtype.val (List.ofFn q) (fun j => primeSubsetPrior Q (Qμ j))
--         childBound pivotBound V F logCellProfile (fun _ => G)
--         (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
--         (fun c => primeSubsetPrior Q (selectedTailCellPrimes A B N Y endpoint D c))
--         (primeSubsetPrior Q bulk) top cs 0 (b + b)
--         (normalizedResidueFamily sets) (normalizedResidueFamily sets) fav
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MovingSlotState`, `OAI.Ostmann.SelectedSmallTailCell`, `OAI.Ostmann.logCellProfile`, `OAI.Ostmann.primeSubsetPrior` and `OAI.Ostmann.selectedTailCellPrimes` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.doubledHalfWeight`, `OAI.Ostmann.initialRegularPrimeRange`, `OAI.Ostmann.initialSmallCellList`, `OAI.Ostmann.initialSpectatorCofactor`, `OAI.Ostmann.primeAlphabetEmbedding`, `OAI.Ostmann.selectedInitialLogCenter`, `OAI.Ostmann.smoothGiantPrimeRange` and `OAI.Ostmann.smoothGiantPrior` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.initialFrozenAmplitude`, `OAI.Ostmann.initialHalfCutoffWeight` and `OAI.Ostmann.initialMovingDataCutoff` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.normalizedResidueFamily`, `OAI.Ostmann.primeHalfTests` and `OAI.Ostmann.scheduledCellAmplitude` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalLeaf` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.twoInfiniteSummandsImpossible_of_published` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/FrozenInitialSmallAmplitude.lean (declaration OAI.Ostmann.frozen_initial_small_amplitude)

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
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem frozen_initial_small_amplitude
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D Qd : Finset ℕ} {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) cs targets)
    (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)] (hP : ∀ p ∈ P, p.Prime)
    (hQP : initialRegularPrimeRange L ⊆ P)
    (hgiant : smoothGiantPrimeRange G ⊆ P)
    (bulk : Finset ℕ) (hbulk : bulk ⊆ initialRegularPrimeRange L)
    (b d : ℕ) (sl sr : Fin d → initialRegularPrimeRange L)
    (hinj : Function.Injective (Fin.append
      (primeAlphabetEmbedding hQP ∘ sl) (primeAlphabetEmbedding hQP ∘ sr)))
    (hsl : ∀ i, (sl i : ℕ) ∈ Qd) (hsr : ∀ i, (sr i : ℕ) ∈ Qd)
    (fallback : initialRegularPrimeRange L)
    (sets : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool) (ψ : 𝓢(ℝ, ℂ))
    (Qμ : ℕ → Finset ℕ) (childBound pivotBound V : ℕ → ℕ)
    (hV0 : (V 0 : ℝ) < Real.exp (G - 1)) :
    let Q := initialRegularPrimeRange L
    let e := primeAlphabetEmbedding hQP
    let cells := initialSmallCellList top cs
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append (e ∘ sl) (e ∘ sr) i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property)
        (hP _ (Fin.append (e ∘ sl) (e ∘ sr) j).property)).mpr
          (fun h => hij (hinj (Subtype.ext h)))
    let _ : ∀ i, Fact (q i).Prime := fun i =>
      ⟨hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property⟩
    let Δ := selectedInitialLogCenter G Y cb cd top cs
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d cells.length cb cd sl sr fallback)
      (fun i => normalizedResidueFamily sets (q i)) (initialSpectatorCofactor q hc) Finset.univ
      (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ))
      (Real.exp (Δ - 2 * (cells.length + 3))) (Real.exp (Δ + 2 * (cells.length + 3)))
    initialFrozenAmplitude P b d cells.length (smoothGiantPrior P logCellProfile G)
      (fun _ => primeSubsetPrior P bulk)
      (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y endpoint D (cells.get i)))
      (Fin.append (primeHalfTests (n := b + (d + cells.length)) P (fun p => sets p) (fun p => fav p))
        (primeHalfTests (n := b + (d + cells.length)) P (fun p => sets p) (fun p => fav p)))
      ψ (Real.exp Y) (V 0)
      (doubledHalfWeight (fun x : Fin (b + (d + cells.length) + 1) → P =>
        (initialHalfCutoffWeight Subtype.val b d cells.length cb cd (Fin.tail x) : ℂ)))
      (e ∘ sl) (e ∘ sr) =
    scheduledCellAmplitude Subtype.val (List.ofFn q) (fun j => primeSubsetPrior Q (Qμ j))
      childBound pivotBound V F logCellProfile (fun _ => G)
      (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
      (fun c => primeSubsetPrior Q (selectedTailCellPrimes A B N Y endpoint D c))
      (primeSubsetPrior Q bulk) top cs 0 (b + b)
      (normalizedResidueFamily sets) (normalizedResidueFamily sets) fav := by
  sorry

end Ostmann

end OAI
end
