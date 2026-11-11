-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_4
-- name    : LargeSupplyFPA.Asymptotic.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:30.646338+00:00
-- url     : https://prove2.me/theorems/f19de523-03a6-48ad-b430-4f9761e6de89
-- title:
--   Lemma 4 — if extremizing pairs stay more than $c$ apart, a length-$c/8$ interval of values in $(\underline\psi_*,\overline\psi_*)$ has optimal utility $\ge\bar u$
-- statement:
--   Fix $\delta\in(0,0.5)$, $H>0$, $\kappa>0$. Consider a sequence of $k$-unit first-price auctions with $n(k)>k$ agents satisfying Assumption 1, and bid profiles $E^{(k)}$ satisfying Assumptions 3 and 4. Let $s$ be any subsequence of unit counts and let $c>0$. Suppose that for every extremizing sequence of bid pairs $\{\underline b^{(k)},\overline b^{(k)}\}$ and every further subsequence $(A^{(s(\theta(l)))})_l$ of $s$ along which the pair is extremizing and the bid difference converges,
--   $$\lim_{l\to\infty}\big(\overline b^{(s(\theta(l)))}-\underline b^{(s(\theta(l)))}\big)>c.$$
--   Then there are a constant $\bar u>0$, a further subsequence $k_m=s(\theta(m))$ and $m^*\in\mathbb N$ such that for all $m>m^*$ there is a closed interval $\mathcal W^{(k_m)}=[a,b]\subset\big(\underline\psi_*^{(k_m)},\overline\psi_*^{(k_m)}\big)$ with
--
--   (a) $b-a\ge c/8$, and
--
--   (b) for every agent $i$ and every value $v\in\mathcal W^{(k_m)}$, the optimal utility $\bar u_i(v)=\sup_{b'\ge0}(v-b')x_i(b')\ge\bar u$.
--
--   At $s=\mathrm{id}$ this is the printed Lemma 4. Lemmas 5 and 6 combine it with the equilibrium condition to bound the width of the critical-bid interval.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: a sequence of k-unit auctions (A^(k))_{k∈ℕ} with n(k) > k agents; subsequences (A^(k_l)) → n : ℕ → ℕ with k < n k, agents Fin (n k), value laws V k and kernels E k indexed by the unit count k (k = 0 included); a subsequence is a strictly increasing φ : ℕ → ℕ and the auction φ l has φ l units; reason: Lean indexing; the term k = 0 does not affect any limit
--   - reading: Assumption 1(a): every value is at most H almost surely (values are non-negative in the model; 1(b) is stated on [0, H]) → V_i([0, H]) = 1 together with the density bound of 1(b), and 0 < H, 0 < κ; reason: the paper's values are non-negative (its bound O(A^(k)) ≥ kζ and W ≥ 0 use it, and p. 6 fixes H > 0, κ > 0); under Assumption 3 alone non-negativity is not implied, so it is read into Assumption 1
--   - encoding: ψ̄_*^(k), ψ̲_*^(k) := min{b ≥ 0 : E[T^(k)(b)] ≤ k ∓ k^(0.5+δ) − 1}, which 'exist for k large enough' → sInf of the same set, equal to its minimum whenever the set is nonempty and 0 for the finitely many k where it is empty; δ ∈ (0, 0.5) is an explicit parameter; reason: only the eventual behaviour of the thresholds enters the statements
--   - encoding: a bid pair {b̲^(k), b̄^(k)} with b̲^(k) ≤ b̄^(k) for every auction (bids are non-negative) → lo, hi : ℕ → ℝ with 0 ≤ lo k ≤ hi k for every k (inside IsExtremizing); reason: bids live in ℝ≥0
--   - generalization: the hypothesis and conclusion refer to subsequences of the whole sequence (A^(k)) → they refer to subsequences of an arbitrary starting subsequence s (StrictMono); the conclusion's subsequence is s ∘ θ; reason: needed by Corollary 1's proof (INSIGHTS I1); at s = id this is exactly the printed lemma, so it specializes to the source
--   - generalization: a corresponding sequence of ϵ-approximate Bayes–Nash equilibria (constant ϵ) → any strategy profiles satisfying Assumptions 3 and 4; no equilibrium hypothesis; reason: the conclusion concerns optimal utility only and the proof (via Lemmas 1, 3 and Fact 3) uses no equilibrium property; the printed lemma is the special case
--   - reading: an interval W^(k_m) ⊂ (ψ̲_*^(k_m), ψ̄_*^(k_m)) with len ≥ c/8 → a closed interval [a, b] with ψ̲ < a, a + c/8 ≤ b, b < ψ̄; reason: the type of interval is not specified; a closed interval contains every other interval with the same endpoints, and the proof constructs the closed interval [ψ̄ − c/4, ψ̄ − c/8]
--   - encoding: the bid difference converges along the subsequence and its limit exceeds c → for every L with Tendsto (b̄ − b̲) atTop (𝓝 L), c < L; reason: same statement
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 20, Lemma 4 (proof pp. 20–21)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
import Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

theorem lemma_4 (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5) (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ)
    (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hA3 : Assumption3 n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (s : ℕ → ℕ) (hs : StrictMono s) (c : ℝ) (hc : 0 < c)
    (hwide : ∀ (lo hi : ℕ → ℝ) (θ : ℕ → ℕ), StrictMono θ → IsExtremizing n V E lo hi (s ∘ θ) →
      ∀ L : ℝ, Tendsto (fun l => hi (s (θ l)) - lo (s (θ l))) atTop (𝓝 L) → c < L) :
    ∃ ubar : ℝ, 0 < ubar ∧ ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ mstar : ℕ, ∀ m : ℕ, mstar < m →
      ∃ a b : ℝ, lowThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) < a ∧ a + c / 8 ≤ b ∧
        b < highThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) ∧
        ∀ i : Fin (n (s (θ m))), ∀ v ∈ Set.Icc a b,
          ubar ≤ optUtility (s (θ m)) (V (s (θ m))) (E (s (θ m))) i v := by sorry

end LargeSupplyFPA.Asymptotic
