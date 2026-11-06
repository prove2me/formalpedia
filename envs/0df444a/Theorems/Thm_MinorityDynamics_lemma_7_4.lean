-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_7_4
-- name    : MinorityDynamics.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:05.556252+00:00
-- url     : https://prove2.me/theorems/8a4c2241-0be2-492f-a049-d0eab83ea277
-- title:
--   Lemma 7.4 — one round from the central interval
-- statement:
--   Assume $k\ge L^{21/10}$ and $k=n^{o(1)}$ ($n,k$ odd, $n$ large), and consider the minority chain. Uniformly over initial states $x\in\Omega$:
--
--   1. if $x\in I_*$, then $\Pr_x\big(X_1\le L/n\big)\ge 1-\big(\tfrac{2e}{L}\big)^L$, and $\big(\tfrac{2e}{L}\big)^L=n^{-\omega(1)}$;
--   2. if $x\in I_*^{\mathrm{in}}$, then $\Pr_x(X_1=0)\ge 1-2n^{-1/2}$;
--   3. more precisely, if $x\in I_*^{\mathrm{in}}$, with probability at least $1-2n^{-1/2}$ all agents adopt the current minority opinion: $\Pr(Z=n)=p(x)^n\ge1-2n^{-1/2}$ for the number $Z\sim\mathrm{Bin}(n,p(x))$ of adopters.
--
--   From the central interval, one round either reaches consensus or a state of size at most $L$.
--
--   Differences from the source:
--   - encoding: under (3.1): k ≥ L^{21/10}, k = n^{o(1)}; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N and odd k with (ln n)^{21/10} ≤ k ≤ n^ε; reason: equivalent to the reading "for every sequence k(n) = n^{o(1)}, for all sufficiently large n" (a sequence violating the ε-form infinitely often can be built from counterexamples with k ≤ n^{1/i}); same instances
--   - encoding: states x ∈ Ω = {0, 1/n, …, (n−1)/(2n)} → minority counts s ∈ Fin (n+1) with 2s < n, and x = s/n; reason: Lean convention for the finite state space; same instances
--   - encoding: "all agents adopt the current minority opinion" → P_n(p(x)) = p(x)^n, the probability that Z ∼ Bin(n, p(x)) equals n; reason: Z counts the adopters of the current minority opinion (§2.1, milestone lumping_2_1); same event
--   - encoding: (2e/L)^L = n^{−ω(1)} → ∀ A > 0, ∃ N, ∀ n ≥ N, (2e/ln n)^{ln n} ≤ n^{−A}; reason: definition of n^{−ω(1)}; same content
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 7.4, p.39

import Mathlib
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 7.4 (One round from the central interval)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.39 = PDF p.41): "Assume (3.1)
and consider the actual chain. Uniformly over initial states x,
(a) If x ∈ I∗, then Pr_x(X1 ≤ L/n) ≥ 1 − (2e/L)^L = 1 − n^{−ω(1)}.
(b) If x ∈ Iin∗, then Pr_x(X1 = 0) ≥ 1 − 2n^{−1/2}.
More precisely, with probability at least 1 − 2n^{−1/2}, all agents adopt the current minority
opinion."

Clauses: (a) the explicit bound `1 − (2e/L)^L`, together with `(2e/L)^L = n^{−ω(1)}` (for every
`A > 0`, `(2e/L)^L ≤ n^{−A}` for large `n`); (b) `Pr_x(X₁ = 0) ≥ 1 − 2n^{−1/2}`; and the "more
precisely" clause: the number `Z ∼ Bin(n, p(x))` of agents adopting the current minority opinion
equals `n` with probability `p(x)^n = P_n(p(x)) ≥ 1 − 2n^{−1/2}`.

**Formalization Note** The "more precisely" clause is stated for the count `Z` of adopters, whose
law is `Bin(n, p(x))` (§2.1; milestone `lumping_2_1`). `X₁ ≤ L/n` is the event that the next
minority count is at most `L`. "Under (3.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε`. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_7_4 :
    (∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k →
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
      ∀ s : Fin (n + 1), InOmega n s →
        (((s : ℕ) : ℝ) / n ∈ Istar n k →
          1 - (2 * Real.exp 1 / logN n) ^ logN n ≤
            ∑ s' ∈ Finset.univ.filter (fun s' : Fin (n + 1) => ((s' : ℕ) : ℝ) / n ≤ logN n / n),
              actualKernel n k s s') ∧
        (((s : ℕ) : ℝ) / n ∈ IstarIn n k →
          1 - 2 * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤ actualKernel n k s 0 ∧
            1 - 2 * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤ binomPMF n (pAdopt k (((s : ℕ) : ℝ) / n)) n)) ∧
    (∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 * Real.exp 1 / logN n) ^ logN n ≤ (n : ℝ) ^ (-A)) := by sorry

end MinorityDynamics
