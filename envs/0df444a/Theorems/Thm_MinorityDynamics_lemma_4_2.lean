-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_4_2
-- name    : MinorityDynamics.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:30.775014+00:00
-- url     : https://prove2.me/theorems/887ad2d6-922b-4993-8a8e-e9a186aefd89
-- title:
--   Lemma 4.2 — the continuous contraction margin (4.6)
-- statement:
--   Assume $k\ge L^{21/10}$ and $k=n^{o(1)}$, with $n,k$ odd and $n$ large. For every surviving state $y\in\mathcal S\cap(K/n,b)$,
--   $$\frac{\alpha(y/k)}{\alpha(y)}+\frac{1}{\alpha(y)\ln(1/y)}\le 1-\frac{1}{8D},$$
--   where $\alpha(x)=A(\ln(1/x))$, $A(t)=1-\frac{9\ln t}{5\ln k}-\frac{t}{8L}$, $K=k/L^{21/20}$ and $D=L/\ln k$.
--
--   The two terms are the lower- and middle-branch contributions predicted by the continuous calculation; the lemma gives the contraction margin $\Omega(1/D)$ that drives the hitting-time bound.
--
--   Differences from the source:
--   - encoding: under (3.1): k ≥ L^{21/10}, k = n^{o(1)}; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N and odd k with (ln n)^{21/10} ≤ k ≤ n^ε; reason: equivalent to the reading "for every sequence k(n) = n^{o(1)}, for all sufficiently large n" (a sequence violating the ε-form infinitely often can be built from counterexamples with k ≤ n^{1/i}); same instances
--   - encoding: states x ∈ Ω = {0, 1/n, …, (n−1)/(2n)} → minority counts s ∈ Fin (n+1) with 2s < n, and x = s/n; reason: Lean convention for the finite state space; same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 4.2, p.16, (4.6)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_MinorityDynamics_Weights

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 4.2 (The continuous contraction margin)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.16 = PDF p.18), under (3.1):
"For every state y ∈ S ∩ (K/n, b), α(y/k)/α(y) + 1/(α(y) ln(1/y)) ≤ 1 − 1/(8D). (4.6)"

Here `α(x) = A(ln(1/x))` with `A(t) = 1 − 9 ln t/(5 ln k) − t/(8L)` (Definition 4.4), `K = k/L^{21/20}`,
`D = L/ln k`, `b = 1 − e^{−L/k}`, and `S = Ω \ H` with `H = Ω ∩ ([0, K/n] ∪ I∗)`.

**Formalization Note** "Under (3.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε`. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_4_2 :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k →
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
      ∀ s : Fin (n + 1), s ∈ Sset n k → KK n k / n < ((s : ℕ) : ℝ) / n →
        ((s : ℕ) : ℝ) / n < bPt n k →
        alphaW n k (((s : ℕ) : ℝ) / n / k) / alphaW n k (((s : ℕ) : ℝ) / n) +
            1 / (alphaW n k (((s : ℕ) : ℝ) / n) * Real.log (1 / (((s : ℕ) : ℝ) / n))) ≤
          1 - 1 / (8 * DD n k) := by sorry

end MinorityDynamics
