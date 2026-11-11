-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_3
-- name    : LargeSupplyFPA.Asymptotic.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:39.800539+00:00
-- url     : https://prove2.me/theorems/d173b545-5989-4a0f-b9f4-219a997379d9
-- title:
--   Lemma 3 — $\limsup_k\overline\psi_*^{(k)}\le H$
-- statement:
--   Fix $\delta\in(0,0.5)$, $H>0$, $\kappa>0$. Consider a sequence of $k$-unit first-price auctions with $n(k)>k$ agents whose value laws satisfy Assumption 1 with these constants, and whose bid profiles $E^{(k)}$ satisfy Assumption 3 and Assumption 4. Then the high threshold bid satisfies
--   $$\limsup_{k\to\infty}\overline\psi_*^{(k)}\le H,$$
--   where $H$ is the uniform upper bound on values in Assumption 1.
--
--   **Formalization Note** $\limsup\le H$ is stated as: for every $\eta>0$, eventually $\overline\psi_*^{(k)}\le H+\eta$. This is equivalent because $\overline\psi_*^{(k)}\ge0$, and it avoids `Filter.limsup` on ℝ, which takes a junk value on sequences that are not bounded above.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: a sequence of k-unit auctions (A^(k))_{k∈ℕ} with n(k) > k agents; subsequences (A^(k_l)) → n : ℕ → ℕ with k < n k, agents Fin (n k), value laws V k and kernels E k indexed by the unit count k (k = 0 included); a subsequence is a strictly increasing φ : ℕ → ℕ and the auction φ l has φ l units; reason: Lean indexing; the term k = 0 does not affect any limit
--   - reading: Assumption 1(a): every value is at most H almost surely (values are non-negative in the model; 1(b) is stated on [0, H]) → V_i([0, H]) = 1 together with the density bound of 1(b), and 0 < H, 0 < κ; reason: the paper's values are non-negative (its bound O(A^(k)) ≥ kζ and W ≥ 0 use it, and p. 6 fixes H > 0, κ > 0); under Assumption 3 alone non-negativity is not implied, so it is read into Assumption 1
--   - encoding: ψ̄_*^(k), ψ̲_*^(k) := min{b ≥ 0 : E[T^(k)(b)] ≤ k ∓ k^(0.5+δ) − 1}, which 'exist for k large enough' → sInf of the same set, equal to its minimum whenever the set is nonempty and 0 for the finitely many k where it is empty; δ ∈ (0, 0.5) is an explicit parameter; reason: only the eventual behaviour of the thresholds enters the statements
--   - encoding: limsup_{k→∞} ψ̄_*^(k) ≤ H → ∀ η > 0, ∀ᶠ k in atTop, ψ̄_*^(k) ≤ H + η; reason: equivalent for a sequence bounded below (ψ̄ ≥ 0); avoids the real limsup's junk value
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 18, Lemma 3

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

theorem lemma_3 (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5) (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ)
    (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hA3 : Assumption3 n V E) (hA4 : ∀ k, IsAtomless (V k) (E k)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, highThreshold δ k (V k) (E k) ≤ H + η := by sorry

end LargeSupplyFPA.Asymptotic
