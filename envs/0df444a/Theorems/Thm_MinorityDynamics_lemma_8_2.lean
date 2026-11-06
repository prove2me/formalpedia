-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_8_2
-- name    : MinorityDynamics.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:16.295297+00:00
-- url     : https://prove2.me/theorems/f05a03a9-94f4-4e1a-bbb7-4322e3a16b99
-- title:
--   Lemma 8.2 — changing several Bernoulli trials to fixed values
-- statement:
--   Assume $k\ge L^{21/10}$ and $k=n^{o(1)}$ ($n,k$ odd, $n$ large), and let $1\le\varrho\le\frac14\sqrt{K/L}$. For $0<p\le1/2$ and $\beta\in\{0,\varrho\}$ let
--   $$P\sim\mathrm{Bin}(n,p),\qquad Z=\beta+\mathrm{Bin}(n-\varrho,p).$$
--   There is a set $\mathcal E=\mathcal E(\beta,p)\subseteq\{0,\dots,n\}$ with $\Pr(Z\in\mathcal E)\le n^{-2}$ such that for every $r\notin\mathcal E$ with $\min\{r,n-r\}>K$,
--   $$\frac{\Pr(Z=r)}{\Pr(P=r)}\le 1+8\varrho\sqrt{\frac LK}.\qquad(8.4)$$
--
--   Fixing the outcome of $\varrho$ of the $n$ trials (the sources) changes the transition probabilities into non-small states by at most a factor $1+8\varrho\sqrt{L/K}$, apart from a negligible exceptional set.
--
--   Differences from the source:
--   - encoding: under (3.1): k ≥ L^{21/10}, k = n^{o(1)}; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N and odd k with (ln n)^{21/10} ≤ k ≤ n^ε; reason: equivalent to the reading "for every sequence k(n) = n^{o(1)}, for all sufficiently large n" (a sequence violating the ε-form infinitely often can be built from counterexamples with k ≤ n^{1/i}); same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 8.2, p.42, (8.4)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 8.2 (Changing several Bernoulli trials to fixed values)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.42 = PDF p.44):
"Assume (3.1), and suppose that 1 ≤ ϱ ≤ (1/4)√(K/L). For 0 < p ≤ 1/2 and β ∈ {0, ϱ}, let
P ∼ Bin(n, p), Z = β + Bin(n − ϱ, p). There exists a set E = E(β, p) ⊆ {0, . . . , n} satisfying
Pr(Z ∈ E) ≤ n^{−2}, such that, for every r ∉ E with min{r, n − r} > K,
Pr(Z = r)/Pr(P = r) ≤ 1 + 8ϱ √(L/K). (8.4)"

**Formalization Note** `Pr(P = r) = P_r(p) > 0` for `0 < p ≤ 1/2` and `r ≤ n`, so the ratio is an
honest quotient. `E` is a finite set of integers in `{0, …, n}`.
"Under (3.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε`. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_8_2 :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k →
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
      ∀ ϱ : ℕ, 1 ≤ ϱ → (ϱ : ℝ) ≤ (1 / 4) * Real.sqrt (KK n k / logN n) →
      ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∀ β : ℕ, (β = 0 ∨ β = ϱ) →
        ∃ E : Finset ℕ, E ⊆ Finset.range (n + 1) ∧
          ∑ r ∈ E, shiftBinomPMF n ϱ β p r ≤ 1 / (n : ℝ) ^ 2 ∧
          ∀ r : ℕ, r ≤ n → r ∉ E → KK n k < ((min r (n - r) : ℕ) : ℝ) →
            shiftBinomPMF n ϱ β p r / binomPMF n p r ≤
              1 + 8 * ϱ * Real.sqrt (logN n / KK n k) := by sorry

end MinorityDynamics
