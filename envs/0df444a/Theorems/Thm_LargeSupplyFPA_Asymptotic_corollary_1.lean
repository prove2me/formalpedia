-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_corollary_1
-- name    : LargeSupplyFPA.Asymptotic.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:41.634295+00:00
-- url     : https://prove2.me/theorems/94ae1f1b-49e1-4f74-ae13-3401a8fe1d03
-- title:
--   Corollary 1 — atomless asymptotically exact equilibria: $\liminf_k W/O=1$
-- statement:
--   Let $H>0$ and $\kappa>0$. Consider a sequence of $k$-unit first-price auctions with $n(k)>k$ agents satisfying Assumption 1, and a sequence of $\epsilon^{(k)}$-approximate Bayes–Nash equilibria $E^{(k)}$ satisfying Assumption 3 and Assumption 4 with $\epsilon^{(k)}\to0$. Then
--   $$\liminf_{k\to\infty}\frac{W(E^{(k)},A^{(k)})}{O(A^{(k)})}=1.$$
--
--   This is part (a) of the main theorem for atomless equilibria that may over-bid by a vanishing amount. Theorem 3 reduces the general case to it.
--
--   **Formalization Note** The ratio lies in $[0,1]$, so `Filter.liminf` on ℝ is the genuine limit inferior.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: a sequence of k-unit auctions (A^(k))_{k∈ℕ} with n(k) > k agents; subsequences (A^(k_l)) → n : ℕ → ℕ with k < n k, agents Fin (n k), value laws V k and kernels E k indexed by the unit count k (k = 0 included); a subsequence is a strictly increasing φ : ℕ → ℕ and the auction φ l has φ l units; reason: Lean indexing; the term k = 0 does not affect any limit
--   - reading: Assumption 1(a): every value is at most H almost surely (values are non-negative in the model; 1(b) is stated on [0, H]) → V_i([0, H]) = 1 together with the density bound of 1(b), and 0 < H, 0 < κ; reason: the paper's values are non-negative (its bound O(A^(k)) ≥ kζ and W ≥ 0 use it, and p. 6 fixes H > 0, κ > 0); under Assumption 3 alone non-negativity is not implied, so it is read into Assumption 1
--   - reading: E_{b∼E_{i,v}}[u_i(v, b)] ≥ sup_{b≥0} u_i(v, b) − ϵ for every v ∈ supp(V_i) → for every v ∈ supp(V_i): b ↦ u_i(v, b) is E_{i,v}-integrable and u_i(v, b) − ϵ ≤ ∫ u_i(v, ·) dE_{i,v} for every b ≥ 0; reason: the ∀ b form is equivalent to the sup form; integrability makes explicit that the paper's expectation is finite (it holds automatically when bids are bounded on the support, as under Assumptions 2 and 3)
--   - encoding: Let ϵ := lim_{k→∞} ϵ^(k) and suppose ϵ = 0 → Tendsto εs atTop (𝓝 0); reason: same hypothesis
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 23, Corollary 1

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

theorem corollary_1 (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ)
    (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (εs : ℕ → ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hBNE : ∀ k, IsApproxBNE k (V k) (E k) (εs k))
    (hA3 : Assumption3 n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (hε : Tendsto εs atTop (𝓝 0)) :
    Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop = 1 := by sorry

end LargeSupplyFPA.Asymptotic
