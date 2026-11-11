-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_1
-- name    : LargeSupplyFPA.Asymptotic.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:45.323034+00:00
-- url     : https://prove2.me/theorems/85d86c80-2774-4106-803d-77b5841d5c41
-- title:
--   Lemma 1 — bid pairs below $\underline\psi_*^{(k)}$ and above $\overline\psi_*^{(k)}$ are extremizing
-- statement:
--   Fix $\delta\in(0,0.5)$. Consider a sequence of $k$-unit first-price auctions with $n(k)>k$ agents and strategy profiles $E^{(k)}$ satisfying Assumption 4 (no marginal bid distribution has an atom). Let $\{\underline b^{(k)},\overline b^{(k)}\}$ be any sequence of bid pairs ($\underline b^{(k)}\le\overline b^{(k)}$) with
--   $$\underline b^{(k)}\in\big[0,\underline\psi_*^{(k)}\big],\qquad \overline b^{(k)}\in\big[\overline\psi_*^{(k)},\infty\big).$$
--   Then the sequence is extremizing over the whole sequence of auctions: $B^{(k)}(\underline b^{(k)})\to0$ and $B^{(k)}(\overline b^{(k)})\to1$.
--
--   This lemma says the $k$-th highest bid concentrates between the two threshold bids. It is the source of the extremizing pairs used in Lemmas 4–6.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: a sequence of k-unit auctions (A^(k))_{k∈ℕ} with n(k) > k agents; subsequences (A^(k_l)) → n : ℕ → ℕ with k < n k, agents Fin (n k), value laws V k and kernels E k indexed by the unit count k (k = 0 included); a subsequence is a strictly increasing φ : ℕ → ℕ and the auction φ l has φ l units; reason: Lean indexing; the term k = 0 does not affect any limit
--   - encoding: ψ̄_*^(k), ψ̲_*^(k) := min{b ≥ 0 : E[T^(k)(b)] ≤ k ∓ k^(0.5+δ) − 1}, which 'exist for k large enough' → sInf of the same set, equal to its minimum whenever the set is nonempty and 0 for the finitely many k where it is empty; δ ∈ (0, 0.5) is an explicit parameter; reason: only the eventual behaviour of the thresholds enters the statements
--   - encoding: a bid pair {b̲^(k), b̄^(k)} with b̲^(k) ≤ b̄^(k) for every auction (bids are non-negative) → lo, hi : ℕ → ℝ with 0 ≤ lo k ≤ hi k for every k (inside IsExtremizing); reason: bids live in ℝ≥0
--   - generalization: the auctions of the sequence satisfy the standing Assumption 1 of §2 (and the profiles are the equilibria E^(k)) → any value laws and any strategy profiles with Assumption 4; no equilibrium property, no Assumption 1; reason: the statement and proof concern the bid distributions only; the printed lemma is the special case
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 15, Lemma 1 (proof p. 16)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
import Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

theorem lemma_1 (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5)
    (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (hseq : IsAuctionSequence n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (lo hi : ℕ → ℝ) (hpair : ∀ k, lo k ≤ hi k)
    (hlo : ∀ k, 0 ≤ lo k ∧ lo k ≤ lowThreshold δ k (V k) (E k))
    (hhi : ∀ k, highThreshold δ k (V k) (E k) ≤ hi k) :
    IsExtremizing n V E lo hi id := by sorry

end LargeSupplyFPA.Asymptotic
