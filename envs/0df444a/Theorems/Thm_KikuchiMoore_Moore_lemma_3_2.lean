-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_3_2
-- name    : KikuchiMoore.Moore.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:52.538746+00:00
-- url     : https://prove2.me/theorems/533dca5c-09e9-4cf8-8600-603691bfdb51
-- title:
--   Lemma 3.2 — Slice ratio lower bound
-- statement:
--   Let $k\ge3$, $2k\le\ell$, $100k\ell\le n$, and $1\le q\le k$. Then
--
--   $$\frac{\binom{n-2q}{\ell-q}}{\binom n\ell}\ge\frac9{10}\left(\frac2e\right)^q\left(\frac\ell n\right)^q.$$
--
--   This slice-count bound is stated for both parities of $k$.
--
--   Differences from the source:
--   - encoding: binomial counts and their quotient → natural binomial coefficients cast to reals before division; reason: the central range prevents truncated subtractions or a zero denominator
--   - generalization: Section 3's standing even arity k = 2r ≥ 4 → any arity k ≥ 3 of either parity; reason: the source states the lemma for general q so that the odd case can reuse it (p. 19), the bound involves k only through 1 ≤ q ≤ k and (3.1), and every even k ≥ 4 is an instance
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 3.2, printed p. 13 = PDF p. 13, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Core

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_3_2 {n k l q : ℕ} (hk : 3 ≤ k) (hc : Central n k l)
    (hq : 1 ≤ q) (hqk : q ≤ k) :
    (9/10 : ℝ) * (2 / Real.exp 1)^q * ((l : ℝ)/n)^q ≤
      (Nat.choose (n-2*q) (l-q) : ℝ) / Nat.choose n l := by sorry

end KikuchiMoore.Moore
