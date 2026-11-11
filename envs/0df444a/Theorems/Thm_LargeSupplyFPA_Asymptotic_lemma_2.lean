-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_2
-- name    : LargeSupplyFPA.Asymptotic.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:57.457472+00:00
-- url     : https://prove2.me/theorems/551ed29c-0852-4c85-80db-db4d461e2874
-- title:
--   Lemma 2 — allocation probability at bids below $\underline\psi_*^{(k)}$ vanishes uniformly
-- statement:
--   Fix $\delta\in(0,0.5)$. Consider a sequence of $k$-unit first-price auctions with $n(k)>k$ agents whose bid distributions $E^{(k)}$ satisfy Assumption 4. For any bids $\underline b^{(k)}\in[0,\underline\psi_*^{(k)}]$,
--   $$\lim_{k\to\infty}\ \max_{i\in N^{(k)}}x_i^{(k)}\big(\underline b^{(k)}\big)=0.$$
--
--   Lemma 1 only controls the $k$-th order statistic, which bounds the allocation probability from below (Fact 3). Lemma 2 bounds every agent's allocation probability from above, which is needed in Lemmas 5 and 6.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: a sequence of k-unit auctions (A^(k))_{k∈ℕ} with n(k) > k agents; subsequences (A^(k_l)) → n : ℕ → ℕ with k < n k, agents Fin (n k), value laws V k and kernels E k indexed by the unit count k (k = 0 included); a subsequence is a strictly increasing φ : ℕ → ℕ and the auction φ l has φ l units; reason: Lean indexing; the term k = 0 does not affect any limit
--   - encoding: ψ̄_*^(k), ψ̲_*^(k) := min{b ≥ 0 : E[T^(k)(b)] ≤ k ∓ k^(0.5+δ) − 1}, which 'exist for k large enough' → sInf of the same set, equal to its minimum whenever the set is nonempty and 0 for the finitely many k where it is empty; δ ∈ (0, 0.5) is an explicit parameter; reason: only the eventual behaviour of the thresholds enters the statements
--   - generalization: E^(k) are the equilibrium bid distributions of the sequence (standing Assumption 1 of §2) → any value laws and strategy profiles with Assumption 4; no equilibrium property, no Assumption 1; reason: the proof uses only Assumption 4 and Chernoff bounds; the printed lemma is the special case
--   - encoding: max_{i∈N^(k)} → ⨆ over i : Fin (n k), a finite nonempty index set since n k > k ≥ 0; reason: same value
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 17, Lemma 2 (proof pp. 17–18)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

theorem lemma_2 (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5)
    (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (hseq : IsAuctionSequence n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k ∧ b k ≤ lowThreshold δ k (V k) (E k)) :
    Tendsto (fun k => ⨆ i : Fin (n k), alloc k (V k) (E k) i (b k)) atTop (𝓝 0) := by sorry

end LargeSupplyFPA.Asymptotic
