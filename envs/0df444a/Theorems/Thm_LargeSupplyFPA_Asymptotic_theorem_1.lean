-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_theorem_1
-- name    : LargeSupplyFPA.Asymptotic.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:49.367246+00:00
-- url     : https://prove2.me/theorems/10a33d0a-2145-476a-8fc5-30a31179df58
-- title:
--   Theorem 1 — an extremizing bid-pair sequence with limiting area $\le c$ gives $\liminf W/O\ge 1-c/\zeta-\epsilon/\zeta$
-- statement:
--   Fix $H>0$ and $\kappa>0$. There is a constant $\zeta>0$, depending only on $H$ and $\kappa$, with the following property. Consider any sequence of $k$-unit first-price auctions $A^{(k)}$ (with $n(k)>k$ agents) satisfying Assumption 1 with these $H,\kappa$, and any corresponding sequence $E^{(k)}$ of $\epsilon^{(k)}$-approximate Bayes–Nash equilibria satisfying Assumption 3, with $\epsilon:=\lim_k\epsilon^{(k)}$. Let $c\ge0$, and let $\{\underline b^{(k)},\overline b^{(k)}\}$ be an extremizing sequence of bid pairs along a subsequence $(A^{(k_l)})_l$ such that
--   $$\lim_{l\to\infty}\int_{\underline b^{(k_l)}}^{\overline b^{(k_l)}}B^{(k_l)}(b)\,db\le c.$$
--   Then
--   $$\liminf_{l\to\infty}\frac{W(E^{(k_l)},A^{(k_l)})}{O(A^{(k_l)})}\ \ge\ 1-\frac{c}{\zeta}-\frac{\epsilon}{\zeta}.$$
--
--   This is the asymptotic smoothness framework. The limiting area under the critical-bid distribution between an extremizing pair, plus the best-response slack, controls the limiting welfare loss.
--
--   **Formalization Note** $\zeta$ is chosen after $H,\kappa$ and before the sequence, $n(\cdot)$, $\epsilon$ and $c$. The paper's proof gives $O(A^{(k)})\ge k\zeta$ with $\zeta=\kappa H^2/2$. The ratio lies in $[0,1]$, so the real `Filter.liminf` is the genuine one.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: a sequence of k-unit auctions (A^(k))_{k∈ℕ} with n(k) > k agents; subsequences (A^(k_l)) → n : ℕ → ℕ with k < n k, agents Fin (n k), value laws V k and kernels E k indexed by the unit count k (k = 0 included); a subsequence is a strictly increasing φ : ℕ → ℕ and the auction φ l has φ l units; reason: Lean indexing; the term k = 0 does not affect any limit
--   - reading: Assumption 1(a): every value is at most H almost surely (values are non-negative in the model; 1(b) is stated on [0, H]) → V_i([0, H]) = 1 together with the density bound of 1(b), and 0 < H, 0 < κ; reason: the paper's values are non-negative (its bound O(A^(k)) ≥ kζ and W ≥ 0 use it, and p. 6 fixes H > 0, κ > 0); under Assumption 3 alone non-negativity is not implied, so it is read into Assumption 1
--   - reading: E_{b∼E_{i,v}}[u_i(v, b)] ≥ sup_{b≥0} u_i(v, b) − ϵ for every v ∈ supp(V_i) → for every v ∈ supp(V_i): b ↦ u_i(v, b) is E_{i,v}-integrable and u_i(v, b) − ϵ ≤ ∫ u_i(v, ·) dE_{i,v} for every b ≥ 0; reason: the ∀ b form is equivalent to the sup form; integrability makes explicit that the paper's expectation is finite (it holds automatically when bids are bounded on the support, as under Assumptions 2 and 3)
--   - encoding: Let ϵ := lim_{k→∞} ϵ^(k) → a hypothesis Tendsto εs atTop (𝓝 ε); reason: the limit is assumed to exist
--   - encoding: a bid pair {b̲^(k), b̄^(k)} with b̲^(k) ≤ b̄^(k) for every auction (bids are non-negative) → lo, hi : ℕ → ℝ with 0 ≤ lo k ≤ hi k for every k (inside IsExtremizing); reason: bids live in ℝ≥0
--   - reading: ζ > 0 is a constant that depends on the parameters of the environment → ∃ ζ > 0 quantified after H, κ and before the sequence, n(·), ϵ, c and the bid pairs; reason: p. 6 names H and κ as the parameters of the environment; a ζ depending on the sequence would make the bound vacuous
--   - encoding: lim_{l→∞} ∫_{b̲^(k_l)}^{b̄^(k_l)} B^(k_l)(b) db ≤ c (the limit exists) → ∃ L, Tendsto (∫_{b̲^(k_l)}^{b̄^(k_l)} B^(k_l)(b) db) atTop (𝓝 L) ∧ L ≤ c; reason: the printed limit is assumed to exist
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 11, Theorem 1 (proof pp. 12–14)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

theorem theorem_1 (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ) :
    ∃ ζ : ℝ, 0 < ζ ∧
      ∀ (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
        (εs : ℕ → ℝ) (ε : ℝ),
        IsAuctionSequence n V E →
        (∀ k, Assumption1 H κ (V k)) →
        (∀ k, IsApproxBNE k (V k) (E k) (εs k)) →
        Assumption3 n V E →
        Tendsto εs atTop (𝓝 ε) →
        ∀ (c : ℝ), 0 ≤ c →
        ∀ (lo hi : ℕ → ℝ) (φ : ℕ → ℕ), IsExtremizing n V E lo hi φ →
        (∃ L : ℝ, Tendsto (fun l => ∫ b in lo (φ l)..hi (φ l),
            kthBidCDF (φ l) (V (φ l)) (E (φ l)) b) atTop (𝓝 L) ∧ L ≤ c) →
        1 - c / ζ - ε / ζ ≤
          Filter.liminf (fun l => welfareRatio (φ l) (V (φ l)) (E (φ l))) atTop := by sorry

end LargeSupplyFPA.Asymptotic
