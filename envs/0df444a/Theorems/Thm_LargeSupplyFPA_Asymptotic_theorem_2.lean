-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_theorem_2
-- name    : LargeSupplyFPA.Asymptotic.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:38.18058+00:00
-- url     : https://prove2.me/theorems/cef4e32c-40c0-44a1-a308-23111be589dc
-- title:
--   Theorem 2 — as supply grows, exact equilibria become fully efficient and $\epsilon$-approximate ones lose at most $\zeta\epsilon(1+\log(H/\epsilon))$
-- statement:
--   Fix $H>0$ and $\kappa>0$. There is a constant $\zeta>0$, depending only on $H$ and $\kappa$, such that the following holds. Take any sequence of $k$-unit first-price auctions $A^{(k)}$ with $n(k)>k$ unit-demand agents and independent values satisfying Assumption 1 with these constants. Take any sequence of $\epsilon^{(k)}$-approximate Bayes–Nash equilibria $E^{(k)}$ (mixed strategies, uniform tie-breaking) satisfying no over-bidding (Assumption 2), with $\epsilon:=\lim_k\epsilon^{(k)}$. Then:
--
--   (a) if $\epsilon=0$, then
--   $$\liminf_{k\to\infty}\frac{W(E^{(k)},A^{(k)})}{O(A^{(k)})}=1;$$
--
--   (b) if $\epsilon\in(0,H)$, then
--   $$\liminf_{k\to\infty}\frac{W(E^{(k)},A^{(k)})}{O(A^{(k)})}\ \ge\ 1-\zeta\,\epsilon\Big(1+\log\frac H\epsilon\Big).$$
--
--   Here $W$ is expected equilibrium welfare (39) and $O$ is the expected sum of the $k$ highest values. Part (a) says the price of anarchy of the multi-unit first-price auction tends to 1 as supply grows. Part (b) says $\epsilon$-approximate best responses cost at most $O(\epsilon\log(1/\epsilon))$ of the optimal welfare in the limit. No atomlessness, symmetry, or finiteness of supports is assumed.
--
--   **Formalization Note** $\zeta$ is chosen after $H,\kappa$ and before $n(\cdot)$, the sequences and $\epsilon$; one $\zeta$ serves both parts. The ratio lies in $[0,1]$, so `Filter.liminf` on ℝ is the genuine limit inferior.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: a sequence of k-unit auctions (A^(k))_{k∈ℕ} with n(k) > k agents; subsequences (A^(k_l)) → n : ℕ → ℕ with k < n k, agents Fin (n k), value laws V k and kernels E k indexed by the unit count k (k = 0 included); a subsequence is a strictly increasing φ : ℕ → ℕ and the auction φ l has φ l units; reason: Lean indexing; the term k = 0 does not affect any limit
--   - encoding: Assumption 1(a): every value is at most H almost surely; H > 0, κ > 0 (p. 6) → V_i([0, H]) = 1 together with the density bound of 1(b), and 0 < H, 0 < κ; reason: equivalent here: under no over-bidding with non-negative bids every support value is ≥ 0, so V_i([0, ∞)) = 1 already follows from the hypotheses
--   - encoding: E_{b∼E_{i,v}}[u_i(v, b)] ≥ sup_{b≥0} u_i(v, b) − ϵ for every v ∈ supp(V_i) → for every v ∈ supp(V_i): b ↦ u_i(v, b) is E_{i,v}-integrable and u_i(v, b) − ϵ ≤ ∫ u_i(v, ·) dE_{i,v} for every b ≥ 0; reason: the ∀ b form is equivalent to the sup form; under Assumption 2 bids lie in [0, v] almost surely and x_i is monotone, so the utility is bounded and measurable and integrability is automatic
--   - encoding: Assumption 2: for any agent i and value v, the bid E_{i,v} is at most v almost surely → for every v ∈ supp(V_i), E_{i,v}((−∞, v]) = 1; reason: values outside the closed support form a V_i-null set and enter no quantity of the theorem (marginal bids, ϵ-BNE, W, O), so the two hypotheses admit the same auctions up to null sets
--   - encoding: Let ϵ := lim_{k→∞} ϵ^(k) → a hypothesis Tendsto εs atTop (𝓝 ε); reason: the limit is assumed to exist
--   - reading: ζ > 0 is a constant that depends on the parameters of the environment → ∃ ζ > 0 quantified after H, κ and before n(·), the sequences and ϵ, shared by (a) and (b); reason: p. 6: H, κ are the parameters of the environment and ϵ is fixed separately; a ζ depending on ϵ or on the sequence would make (b) vacuous
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 14, Theorem 2 (proof §4.4, p. 28)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

theorem theorem_2 (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ) :
    ∃ ζ : ℝ, 0 < ζ ∧
      ∀ (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
        (εs : ℕ → ℝ) (ε : ℝ),
        IsAuctionSequence n V E →
        (∀ k, Assumption1 H κ (V k)) →
        (∀ k, IsApproxBNE k (V k) (E k) (εs k)) →
        (∀ k, NoOverbidding (V k) (E k)) →
        Tendsto εs atTop (𝓝 ε) →
        (ε = 0 → Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop = 1) ∧
        (ε ∈ Set.Ioo 0 H →
          1 - ζ * ε * (1 + Real.log (H / ε)) ≤
            Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop) := by sorry

end LargeSupplyFPA.Asymptotic
