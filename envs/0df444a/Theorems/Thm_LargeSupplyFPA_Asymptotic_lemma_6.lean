-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_6
-- name    : LargeSupplyFPA.Asymptotic.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:39.968214+00:00
-- url     : https://prove2.me/theorems/5200fc74-0cac-47cd-ae78-b6738afd7acf
-- title:
--   Lemma 6 — atomless $\epsilon^*$-approximate equilibria: $\liminf_k W/O\ge1-\zeta'\epsilon^*(1+\log(H/\epsilon^*))$
-- statement:
--   Fix $H>0$ and $\kappa>0$. There is a constant $\zeta'>0$, depending only on $H$ and $\kappa$, such that the following holds. Take any sequence of $k$-unit first-price auctions with $n(k)>k$ agents satisfying Assumption 1, and any sequence of $\epsilon^{(k)}$-approximate Bayes–Nash equilibria satisfying Assumptions 3 and 4, with $\epsilon^*:=\lim_k\epsilon^{(k)}\in(0,H)$. Then
--   $$\liminf_{k\to\infty}\frac{W(E^{(k)},A^{(k)})}{O(A^{(k)})}\ \ge\ 1-\zeta'\epsilon^*\Big(1+\log\frac{H}{\epsilon^*}\Big).$$
--
--   This is part (b) of the main theorem for atomless equilibria. The paper's proof gives $\zeta'=(2+\log(4/3))/\zeta$, with $\zeta$ the constant of Theorem 1.
--
--   **Formalization Note** $\zeta'$ is chosen after $H,\kappa$ and before the sequence and $\epsilon^*$. A $\zeta'$ depending on $\epsilon^*$ would make the bound vacuous.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: a sequence of k-unit auctions (A^(k))_{k∈ℕ} with n(k) > k agents; subsequences (A^(k_l)) → n : ℕ → ℕ with k < n k, agents Fin (n k), value laws V k and kernels E k indexed by the unit count k (k = 0 included); a subsequence is a strictly increasing φ : ℕ → ℕ and the auction φ l has φ l units; reason: Lean indexing; the term k = 0 does not affect any limit
--   - reading: Assumption 1(a): every value is at most H almost surely (values are non-negative in the model; 1(b) is stated on [0, H]) → V_i([0, H]) = 1 together with the density bound of 1(b), and 0 < H, 0 < κ; reason: the paper's values are non-negative (its bound O(A^(k)) ≥ kζ and W ≥ 0 use it, and p. 6 fixes H > 0, κ > 0); under Assumption 3 alone non-negativity is not implied, so it is read into Assumption 1
--   - reading: E_{b∼E_{i,v}}[u_i(v, b)] ≥ sup_{b≥0} u_i(v, b) − ϵ for every v ∈ supp(V_i) → for every v ∈ supp(V_i): b ↦ u_i(v, b) is E_{i,v}-integrable and u_i(v, b) − ϵ ≤ ∫ u_i(v, ·) dE_{i,v} for every b ≥ 0; reason: the ∀ b form is equivalent to the sup form; integrability makes explicit that the paper's expectation is finite (it holds automatically when bids are bounded on the support, as under Assumptions 2 and 3)
--   - encoding: Let ϵ := lim_{k→∞} ϵ^(k) → a hypothesis Tendsto εs atTop (𝓝 ε); reason: the limit is assumed to exist
--   - reading: ζ′ > 0 is a constant that depends on the parameters of the environment → ∃ ζ′ > 0 quantified after H, κ and before the sequence, n(·) and ϵ*; reason: p. 6 names H and κ as the parameters; the proof's ζ′ = (2 + log(4/3))/ζ depends on them only
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 25, Lemma 6 (proof pp. 25–28)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

theorem lemma_6 (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ) :
    ∃ ζ' : ℝ, 0 < ζ' ∧
      ∀ (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
        (εs : ℕ → ℝ) (εstar : ℝ),
        IsAuctionSequence n V E →
        (∀ k, Assumption1 H κ (V k)) →
        (∀ k, IsApproxBNE k (V k) (E k) (εs k)) →
        Assumption3 n V E →
        (∀ k, IsAtomless (V k) (E k)) →
        Tendsto εs atTop (𝓝 εstar) →
        εstar ∈ Set.Ioo 0 H →
        1 - ζ' * εstar * (1 + Real.log (H / εstar)) ≤
          Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop := by sorry

end LargeSupplyFPA.Asymptotic
