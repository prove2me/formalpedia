-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_3_2
-- name    : MinorityDynamics.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:23.343908+00:00
-- url     : https://prove2.me/theorems/249e4a65-8b92-4c9f-a7e3-5e1ed37ade5f
-- title:
--   Lemma 3.2 — consensus from $\mathcal H$: $\Pr_x(\tau_0>D+2)\le 4n^{-1/2}$
-- statement:
--   Assume (1.1): $k\ge L^{21/10}$, $k=n^{o(1)}$ and $2\ln n\le k^d/n\le\frac15(\ln n)^{21/20}$ for some $d\in\mathbb N$ ($n,k$ odd, $n$ large). For every initial state $x\in\mathcal H$ of the minority chain,
--   $$\Pr_x\big(\tau_0>D+2\big)\le 4n^{-1/2},\qquad \tau_0=\inf\{t\ge0:X_t=0\}.$$
--
--   This is the second half of the proof of Theorem 1.1: from a small minority or the central interval, consensus follows within $D+2$ rounds.
--
--   Differences from the source:
--   - encoding: under (1.1): k ≥ L^{21/10}, k = n^{o(1)}, 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} for some d ∈ ℕ; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N, odd k and d ∈ ℕ with (ln n)^{21/10} ≤ k ≤ n^ε and 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} (real quotient); reason: equivalent to the sequence reading of k = n^{o(1)} for all sufficiently large n; "for some d" in a hypothesis is "for every d" satisfying it; same instances
--   - encoding: states x ∈ Ω = {0, 1/n, …, (n−1)/(2n)} → minority counts s ∈ Fin (n+1) with 2s < n, and x = s/n; reason: Lean convention for the finite state space; same instances
--   - encoding: Pr_x(τ_A > T) for the hitting time τ_A and a real T ≥ 0 → avoidProb P A ⌊T⌋₊ x: the probability, defined by the first-step recursion, that the chain avoids A at rounds 0, …, ⌊T⌋; reason: τ_A is an integer, so τ_A > T iff τ_A > ⌊T⌋; the recursion is the law of the chain; same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 3.2, p.13

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 3.2 (Consensus from H)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.13 = PDF p.15): "Under (1.1), for any initial
configuration x ∈ H, Pr_x(τ0 > D + 2) ≤ 4n^{−1/2}."

For the minority chain started at `x = s/n ∈ H`, the probability of not having reached consensus
(state `0`) by round `⌊D + 2⌋` is at most `4n^{−1/2}`.

**Formalization Note** `τ₀ > D + 2` is `τ₀ > ⌊D + 2⌋` (`τ₀` is an integer).
"Assume (1.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`, `2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20}` for some `d ∈ ℕ`, with a real quotient `k^d/n`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε` and every `d` satisfying the residue condition. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_3_2 :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k → ∀ d : ℕ,
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
    2 * Real.log n ≤ (k : ℝ) ^ d / n → (k : ℝ) ^ d / n ≤ (1 / 5) * Real.log n ^ ((21 : ℝ) / 20) →
      ∀ s : Fin (n + 1), s ∈ Hset n k →
        avoidProb (actualKernel n k) {(0 : Fin (n + 1))} ⌊DD n k + 2⌋₊ s ≤
          4 * (n : ℝ) ^ (-(1 : ℝ) / 2) := by sorry

end MinorityDynamics
