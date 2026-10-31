-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_half_log_good_masked_whole_shell_rate
-- name    : OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_masked_whole_shell_rate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:28:32.447766+00:00
-- url     : https://prove2.me/theorems/7d0c94d5-18f4-4c2f-bb82-dd85c07515dc
-- title:
--   OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_masked_whole_shell_rate (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_masked_whole_shell_rate` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternHalfLogGoodMaskedShell.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternHalfLogGoodMaskedShell.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter MeasureTheory`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.movingPattern_half_log_good_masked_whole_shell_rate
--       (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
--       (A Wwin Bφ Dφ Cmass gain : ℝ)
--       (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
--       (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
--       (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
--       (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
--       (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
--       ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
--       ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
--         ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
--         hi - lo ≤ Real.exp (Wwin * m) →
--         ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
--           (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
--           (t : Bool → FrequencyTree ℤ (n + 2))
--           (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) (n + 2)) (Nfreq : ℕ)
--           (small : TreeLeafTuple (List Bidx) (n + 2))
--           (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
--           (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
--           (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
--           (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
--           (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
--           (childBound pivotBound : ℕ → ℕ)
--           (f : ℤ → ℂ)
--           (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2))]
--           (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
--           (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p j)))
--           [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i)]
--           (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
--           (β : Fin m → ℝ)
--           (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
--           (φ : ℝ → ℝ) (G : ℕ → ℝ)
--           (global : Finset ℕ)
--           (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
--           (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)
--           (active : Fin (movingPatternRegularSlots e (n + 2) m small slot).length → Bool)
--           (Eprior αall βint Vint Uall : ℝ)
--           (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
--           (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
--         let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i
--         let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
--           (Real.exp ((6 / 1000 : ℝ) * L))
--         (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
--         1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
--         (∀ b : Bool, ∀ i ∈ flattenMovingSlots (n + 2) ((fun _ => small) b), i ∉ Set.range slot) →
--         (∀ i, (n + 2) ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
--         (∀ b : Bool, MovingLeafLengthLE (n + 2) ((fun _ => small) b) r₀) →
--         t = (fun b => frequencyTreeMap Subtype.val (n + 2) (frequencyPairProjection Sfreq (n + 2) b ft)) →
--         (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
--         (∀ s, ‖f s‖ ≤ 1) →
--         1 ≤ m → (∀ i, primeCutoff ≤ p i) →
--         (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
--         (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
--         4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
--           3 * Fintype.card (TreeLeafIndex (n + 2)) →
--         (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
--         (∀ i, residueDensity (sets i) ≤ 2 / 3) →
--         (∀ i, 2 * β i ≤ ε) →
--         (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
--           ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
--         M ≤ bulkProgressionCutoff L →
--         pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
--           pageAtModulus ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2))
--             (selectedPageZero P (bulkProgressionCutoff L)) →
--         (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
--         (∀ x, 1 ≤ |x| → φ x = 0) →
--         S ⊆ primes →
--         ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
--         (∀ q ∈ outside, q.Prime) →
--         (∀ j, ν (slot j) = primeSubsetPrior primes (S \ global)) →
--         (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
--         (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
--         1 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
--         (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
--         (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
--         (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
--         (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
--         (∀ q : primes, (q : ℝ) ≤ Uall) →
--         (∀ j, active j = false →
--           (movingPatternRegularSlots e (n + 2) m small slot).get j ∉
--             Set.range (movingPatternBulkEmbedding e slot)) →
--         (∀ q ∈ outside, ∃ i, p i = q) →
--         Function.Injective p →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
--         (Nfreq : ℝ) ≤ Real.exp (A * m) →
--         Eprior ≤ Real.exp (Cmass * L) →
--         αall ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
--         βint ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
--         Vint = Real.exp ((1 / 100 : ℝ) * L) →
--         Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) →
--         Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
--         (∀ j, j < (n + 2) → ∀ a, μ j a ≠ 0 → tier a = j) →
--         (∀ j a, ν j a ≠ 0 → tier a = tierB j) →
--         Nfreq ≤ primeLo → Nfreq < cutoff → cutoff ≤ primeLo →
--         (∀ j a, μ j a ≠ 0 → primeLo < (a : ℕ)) →
--         (∀ j a, ν j a ≠ 0 → primeLo < (a : ℕ)) →
--         (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
--         (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q →
--           ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q →
--           ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
--         sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
--         (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
--         ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern
--           (fun x => ((∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
--           movingOriginalPatternMatchedObservable e t small slot perm pattern primes _hprimes
--             p (fun i => normalizedResidueTransform (sets i)) Dq
--             (movingPatternRegularSlots e (n + 2) m small slot).get active sreg
--             (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
--               (movingPatternRegularSlots e (n + 2) m small slot))
--             (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
--             Jleft Jright diagonal uG vG rG sG center x) x‖ ≤
--           ((2 : ℝ) ^ Fintype.card Cidx *
--             (Real.exp (Cmass * L)) ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
--             (Real.exp (-gain * m) +
--               Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
--               4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveRealZero` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.MovingLeafLengthLE`, `OAI.Ostmann.MovingSampleIndex`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.TreeLeafTuple`, `OAI.Ostmann.arrangementGraph`, `OAI.Ostmann.bulkLogCutoffWeight`, `OAI.Ostmann.flattenMovingSlots`, `OAI.Ostmann.instFintypeConnectedComponentSumArrangementGraph`, `OAI.Ostmann.logCellProfile`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.residueDensity` and `OAI.Ostmann.treeLeafIndexFintype` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.bulkProgressionCutoff`, `OAI.Ostmann.bulkResidueModuli`, `OAI.Ostmann.deletedConductorPrime`, `OAI.Ostmann.giantProgressionCutoff`, `OAI.Ostmann.movingRegularOther` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.frequencyModelBase`, `OAI.Ostmann.frequencyPairProjection`, `OAI.Ostmann.frequencyTreeMap`, `OAI.Ostmann.normalizedResidueTransform` and `OAI.Ostmann.pageAtModulus` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.movingPatternBulkEmbedding` and `OAI.Ostmann.movingSampleTier` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.selectedPageZero` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.movingOriginalPatternWeight`, `OAI.Ostmann.movingPatternRegularSlots` and `OAI.Ostmann.normalizedResidueFamily` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalPatternMatchedObservable` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proofs of `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_full_energy` and `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternHalfLogGoodMaskedShell.lean (declaration OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_masked_whole_shell_rate)

import Mathlib
import Definitions.Def_OAIQ095D008

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_half_log_good_masked_whole_shell_rate
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) (n + 2)) (Nfreq : ℕ)
        (small : TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (f : ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i)]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)
        (active : Fin (movingPatternRegularSlots e (n + 2) m small slot).length → Bool)
        (Eprior αall βint Vint Uall : ℝ)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ b : Bool, ∀ i ∈ flattenMovingSlots (n + 2) ((fun _ => small) b), i ∉ Set.range slot) →
      (∀ i, (n + 2) ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b : Bool, MovingLeafLengthLE (n + 2) ((fun _ => small) b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val (n + 2) (frequencyPairProjection Sfreq (n + 2) b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ s, ‖f s‖ ≤ 1) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2))
          (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      S ⊆ primes →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ q ∈ outside, q.Prime) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (S \ global)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      1 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ j, active j = false →
        (movingPatternRegularSlots e (n + 2) m small slot).get j ∉
          Set.range (movingPatternBulkEmbedding e slot)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      Eprior ≤ Real.exp (Cmass * L) →
      αall ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      βint ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
      Vint = Real.exp ((1 / 100 : ℝ) * L) →
      Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
      (∀ j, j < (n + 2) → ∀ a, μ j a ≠ 0 → tier a = j) →
      (∀ j a, ν j a ≠ 0 → tier a = tierB j) →
      Nfreq ≤ primeLo → Nfreq < cutoff → cutoff ≤ primeLo →
      (∀ j a, μ j a ≠ 0 → primeLo < (a : ℕ)) →
      (∀ j a, ν j a ≠ 0 → primeLo < (a : ℕ)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern
        (fun x => ((∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
        movingOriginalPatternMatchedObservable e t small slot perm pattern primes _hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq
          (movingPatternRegularSlots e (n + 2) m small slot).get active sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e (n + 2) m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center x) x‖ ≤
        ((2 : ℝ) ^ Fintype.card Cidx *
          (Real.exp (Cmass * L)) ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
          (Real.exp (-gain * m) +
            Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  sorry

end Ostmann

end OAI
end
