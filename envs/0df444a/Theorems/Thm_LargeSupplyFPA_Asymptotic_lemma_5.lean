-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_5
-- name    : LargeSupplyFPA.Asymptotic.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:39.43801+00:00
-- url     : https://prove2.me/theorems/24f408a5-8183-41e7-ae65-2c1cf85dd840
-- title:
--   Lemma 5 — when $\epsilon^{(k)}\to0$, extremizing bid pairs of limiting width $<c$ exist (inside any subsequence)
-- statement:
--   Let $H>0$ and $\kappa>0$. Consider a sequence of $k$-unit first-price auctions with $n(k)>k$ agents satisfying Assumption 1, and a sequence of $\epsilon^{(k)}$-approximate Bayes–Nash equilibria $E^{(k)}$ satisfying Assumptions 3 and 4 with $\epsilon^{(k)}\to0$. Then for every subsequence $s$ of unit counts and every $c>0$ there are a sequence of bid pairs $\{\underline b^{(k)},\overline b^{(k)}\}$ and a further subsequence $(A^{(s(\theta(l)))})_l$ along which the pairs are extremizing and
--   $$\lim_{l\to\infty}\big(\overline b^{(s(\theta(l)))}-\underline b^{(s(\theta(l)))}\big)<c.$$
--
--   At $s=\mathrm{id}$ this is the printed Lemma 5. In the limit of exact equilibria, the critical bid becomes deterministic along subsequences. Corollary 1 needs this inside an arbitrary subsequence (INSIGHTS I1).
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: a sequence of k-unit auctions (A^(k))_{k∈ℕ} with n(k) > k agents; subsequences (A^(k_l)) → n : ℕ → ℕ with k < n k, agents Fin (n k), value laws V k and kernels E k indexed by the unit count k (k = 0 included); a subsequence is a strictly increasing φ : ℕ → ℕ and the auction φ l has φ l units; reason: Lean indexing; the term k = 0 does not affect any limit
--   - reading: Assumption 1(a): every value is at most H almost surely (values are non-negative in the model; 1(b) is stated on [0, H]) → V_i([0, H]) = 1 together with the density bound of 1(b), and 0 < H, 0 < κ; reason: the paper's values are non-negative (its bound O(A^(k)) ≥ kζ and W ≥ 0 use it, and p. 6 fixes H > 0, κ > 0); under Assumption 3 alone non-negativity is not implied, so it is read into Assumption 1
--   - reading: E_{b∼E_{i,v}}[u_i(v, b)] ≥ sup_{b≥0} u_i(v, b) − ϵ for every v ∈ supp(V_i) → for every v ∈ supp(V_i): b ↦ u_i(v, b) is E_{i,v}-integrable and u_i(v, b) − ϵ ≤ ∫ u_i(v, ·) dE_{i,v} for every b ≥ 0; reason: the ∀ b form is equivalent to the sup form; integrability makes explicit that the paper's expectation is finite (it holds automatically when bids are bounded on the support, as under Assumptions 2 and 3)
--   - generalization: the hypothesis and conclusion refer to subsequences of the whole sequence (A^(k)) → they refer to subsequences of an arbitrary starting subsequence s (StrictMono); the conclusion's subsequence is s ∘ θ; reason: needed by Corollary 1's proof (INSIGHTS I1); at s = id this is exactly the printed lemma, so it specializes to the source
--   - encoding: Let ϵ := lim_{k→∞} ϵ^(k) and suppose ϵ = 0 → Tendsto εs atTop (𝓝 0); reason: same hypothesis
--   - encoding: lim_{l→∞} (b̄^(k_l) − b̲^(k_l)) < c (the limit exists) → ∃ L, Tendsto ((b̄^(k_l) − b̲^(k_l))) atTop (𝓝 L) ∧ L < c; reason: the printed limit is assumed to exist
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 21, Lemma 5 (proof p. 22)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

theorem lemma_5 (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ)
    (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (εs : ℕ → ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hBNE : ∀ k, IsApproxBNE k (V k) (E k) (εs k))
    (hA3 : Assumption3 n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (hε : Tendsto εs atTop (𝓝 0)) :
    ∀ s : ℕ → ℕ, StrictMono s → ∀ c : ℝ, 0 < c →
      ∃ (lo hi : ℕ → ℝ) (θ : ℕ → ℕ), StrictMono θ ∧ IsExtremizing n V E lo hi (s ∘ θ) ∧
        ∃ L : ℝ, Tendsto (fun l => hi (s (θ l)) - lo (s (θ l))) atTop (𝓝 L) ∧ L < c := by sorry

end LargeSupplyFPA.Asymptotic
