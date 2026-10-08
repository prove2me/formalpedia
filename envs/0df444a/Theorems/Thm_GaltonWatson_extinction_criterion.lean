-- Prove2me | Theorems.Thm_GaltonWatson_extinction_criterion
-- name    : GaltonWatson.extinction_criterion
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:52:03.487412+00:00
-- url     : https://prove2.me/theorems/880d0ee6-f5d0-4982-b301-668f019c1428
-- title:
--   Galton–Watson extinction criterion: $q$ is the least root of $f(s)=s$ in $[0,1]$, and $q=1 \iff m\le 1$
-- statement:
--   This is the extinction criterion for the Galton–Watson branching process.
--
--   Let $(p_k)_{k\ge 0}$ be a probability distribution on $\mathbb N=\{0,1,2,\dots\}$ (the *offspring distribution*) with $p_1<1$ and with finite mean
--   $$
--   m=\sum_{k\ge 0}k\,p_k<\infty ,
--   $$
--   and let
--   $$
--   f(s)=\sum_{k\ge 0}p_k\,s^k,\qquad 0\le s\le 1,
--   $$
--   be its probability generating function.
--
--   On a probability space $(\Omega,\mathcal F,\mathbb P)$ let $(\xi_{n,i})_{n,i\ge 0}$ be independent random variables, each with law $\mathbb P(\xi_{n,i}=k)=p_k$ for all $k\in\mathbb N$; $\xi_{n,i}$ is the number of children of the $i$-th individual of generation $n$. The Galton–Watson process $(Z_n)_{n\ge 0}$ is
--   $$
--   Z_0=1,\qquad Z_{n+1}=\sum_{i=0}^{Z_n-1}\xi_{n,i}\quad(n\ge 0),
--   $$
--   where an empty sum is $0$ (so once the population dies out it stays extinct). Let
--   $$
--   q=\mathbb P\bigl(Z_n=0\ \text{for some } n\ge 0\bigr)
--   $$
--   be the extinction probability. Then:
--
--   1. $q$ is the smallest root of the equation $f(s)=s$ in $[0,1]$;
--   2. $q=1$ if and only if $m\le 1$.
--
--   So the population survives forever with positive probability exactly in the supercritical case $m>1$. The hypothesis $p_1<1$ only excludes the degenerate process in which every individual has exactly one child (then $Z_n=1$ for all $n$, so $q=0$ although $m=1$).
--
--   This is the basic dichotomy of branching-process theory (subcritical and critical processes die out, supercritical ones survive with positive probability), and the fixed-point characterization of $q$ is the standard tool for computing extinction probabilities in population genetics, epidemic models, branching random walks and the exploration of random graphs.
--
--   **Formalization Note** The offspring law is a `PMF ℕ`. The mean $m=\sum_k k\,p_k$ is taken in $[0,\infty]$; finiteness is a hypothesis and the comparison $m\le 1$ is made there. The generating function is the real series $\sum_k p_k s^k$ (Lean's convention $0^0=1$ gives $f(0)=p_0$), and "smallest root in $[0,1]$" is `IsLeast` of $\{s\in[0,1] : f(s)=s\}$. The array $(\xi_{n,i})$ is mutually independent as a family indexed by pairs $(n,i)\in\mathbb N\times\mathbb N$, each $\xi_{n,i}$ is measurable with $\mathbb P(\xi_{n,i}=k)=p_k$ for every $k$, and $Z$ is any function satisfying the recursion above (which determines it). The extinction probability is the real-valued measure of the event $\{\exists n,\ Z_n=0\}$.
-- source:
--   K. B. Athreya and P. E. Ney, Branching Processes, Springer 1972, Chapter I, Section 5, Theorem 1 (extinction probability); G. R. Grimmett and D. R. Stirzaker, Probability and Random Processes, 3rd ed., Oxford University Press 2001, Section 5.4, Theorem (5.4.5) (eta is the smallest non-negative root of s = G(s); eta = 1 if mu < 1, eta < 1 if mu > 1, eta = 1 if mu = 1 with positive variance); R. Durrett, Probability: Theory and Examples, 5th ed., Cambridge University Press 2019, Section 4.3.4 (Branching Processes), the extinction theorems for mu < 1, for mu = 1 with P(xi = 1) < 1, and for mu > 1; T. E. Harris, The Theory of Branching Processes, Springer 1963, Chapter I, Section 6 (probability of extinction).

import Mathlib

open MeasureTheory ProbabilityTheory

namespace GaltonWatson

/-- Galton–Watson extinction criterion (Athreya–Ney, Ch. I §5 Thm 1; Grimmett–Stirzaker Thm 5.4.5;
Durrett PTE §4.3.4). The offspring law is `p`, the offspring numbers `ξ n i` (child count of the
`i`-th individual of generation `n`) are iid with law `p`, `Z 0 = 1` and
`Z (n+1) = ∑_{i < Z n} ξ n i`. Then the extinction probability `q = P(∃ n, Z n = 0)` is the
smallest root of `f s = s` in `[0,1]`, where `f s = ∑ p_k s^k`, and `q = 1 ↔ m ≤ 1`. -/
theorem extinction_criterion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : PMF ℕ) (hp1 : p 1 < 1) (hm : ∑' k : ℕ, (k : ENNReal) * p k ≠ ⊤)
    (ξ : ℕ → ℕ → Ω → ℕ) (hξ_meas : ∀ n i, Measurable (ξ n i))
    (hξ_indep : iIndepFun (fun ni : ℕ × ℕ => ξ ni.1 ni.2) P)
    (hξ_law : ∀ n i k, P (ξ n i ⁻¹' {k}) = p k)
    (Z : ℕ → Ω → ℕ) (hZ0 : ∀ ω, Z 0 ω = 1)
    (hZ : ∀ n ω, Z (n + 1) ω = ∑ i ∈ Finset.range (Z n ω), ξ n i ω) :
    IsLeast {s : ℝ | s ∈ Set.Icc 0 1 ∧ ∑' k : ℕ, (p k).toReal * s ^ k = s}
        (P.real {ω | ∃ n, Z n ω = 0}) ∧
      (P.real {ω | ∃ n, Z n ω = 0} = 1 ↔ ∑' k : ℕ, (k : ENNReal) * p k ≤ 1) := by sorry

end GaltonWatson
