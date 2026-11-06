-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_3_1
-- name    : MinorityDynamics.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:39.252257+00:00
-- url     : https://prove2.me/theorems/db9442e0-1312-4f17-8186-a9a75ec4b3c6
-- title:
--   Lemma 3.1 — hitting $\mathcal H$: $\Pr_x(\tau_{\mathcal H}>CDL)\le n^{-1}$
-- statement:
--   Assume $k\ge L^{21/10}$ and $k=n^{o(1)}$ ($n,k$ odd, $n$ large). There is a constant $C>0$ such that for every initial state $x\in\mathcal S$ of the minority chain,
--   $$\Pr_x\big(\tau_{\mathcal H}>CDL\big)\le n^{-1},$$
--   where $\tau_{\mathcal H}=\inf\{t\ge0:X_t\in\mathcal H\}$, $\mathcal H=\Omega\cap([0,K/n]\cup I_*)$ and $D=L/\ln k$.
--
--   This is the first half of the proof of Theorem 1.1: within $O(\ln^2 n/\ln k)$ rounds the chain reaches a small minority or the central interval.
--
--   Differences from the source:
--   - encoding: under (3.1): k ≥ L^{21/10}, k = n^{o(1)}; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N and odd k with (ln n)^{21/10} ≤ k ≤ n^ε; reason: equivalent to the reading "for every sequence k(n) = n^{o(1)}, for all sufficiently large n" (a sequence violating the ε-form infinitely often can be built from counterexamples with k ≤ n^{1/i}); same instances
--   - encoding: states x ∈ Ω = {0, 1/n, …, (n−1)/(2n)} → minority counts s ∈ Fin (n+1) with 2s < n, and x = s/n; reason: Lean convention for the finite state space; same instances
--   - encoding: Pr_x(τ_A > T) for the hitting time τ_A and a real T ≥ 0 → avoidProb P A ⌊T⌋₊ x: the probability, defined by the first-step recursion, that the chain avoids A at rounds 0, …, ⌊T⌋; reason: τ_A is an integer, so τ_A > T iff τ_A > ⌊T⌋; the recursion is the law of the chain; same instances
--   - reading: "there is a constant C > 0" under (3.1)/(1.1) → C is chosen before ε, N, n, k (absolute); reason: the stronger of the two readings (a constant independent of the sequence k(n)); the proof gives a numerical constant
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 3.1, p.13

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 3.1 (Hitting H)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.13 = PDF p.15): "Under (3.1), there is a constant C > 0
such that, for any initial configuration x ∈ S, Pr_x(τH > CDL) ≤ n^{−1}."

For the minority chain started at `x = s/n ∈ S`, the probability of not having entered
`H = Ω ∩ ([0, K/n] ∪ I∗)` by round `⌊CDL⌋` is at most `1/n`.

**Formalization Note** The constant `C` is absolute: it is chosen before `ε`, `N`, `n` and `k`.
`τ_H > CDL` is `τ_H > ⌊CDL⌋` (`τ_H` is an integer), i.e. the chain avoids `H` at rounds
`0, …, ⌊CDL⌋`. "Under (3.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε`. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k →
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
      ∀ s : Fin (n + 1), s ∈ Sset n k →
        avoidProb (actualKernel n k) (Hset n k) ⌊C * DD n k * logN n⌋₊ s ≤ 1 / n := by sorry

end MinorityDynamics
