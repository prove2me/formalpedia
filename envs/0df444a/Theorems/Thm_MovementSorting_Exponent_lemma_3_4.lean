-- Prove2me | Theorems.Thm_MovementSorting_Exponent_lemma_3_4
-- name    : MovementSorting.Exponent.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:02:29.135209+00:00
-- url     : https://prove2.me/theorems/6e618754-145d-4798-b374-98a52365ea58
-- title:
--   Lemma 3.4 — w.h.p. every route visits O(1 + L(b/n)^{1/D}) log n cells of C_b at every dyadic scale b ≤ n^α
-- statement:
--   Fix $d \ge 1$ and a constant $\alpha < 1$. There is a constant $c > 0$ depending only on $d$ and $\alpha$, and a threshold $n_0$, such that for every $m \ge 2$ with $n = m^d \ge n_0$, with probability at least $1 - n^{-10}$ over the uniform input the following holds: for every dyadic scale $b = 2^i \le n^\alpha$ and every route (any start, any length) of movement $L$, the route visits at most $c\,(1 + L(b/n)^{1/D})\log n$ cells of $C_b$.
--
--   Differences from the source:
--   - encoding: "for sufficiently large n" → ∃ n₀ (chosen after c, depending on d and α), for all m ≥ 2 with n₀ ≤ m^d; reason: the threshold of the asymptotic statement made explicit
--   - encoding: dyadic scale b ≤ n^α; every route → b = 2^i for i : ℕ with 2^i ≤ n^α; every list ρ with IsRoute ρ, counted by visitedCount; reason: a dyadic scale is a power of two (Definition 2.4); a route visits a cell when it visits an orientation of it
--   - encoding: a cell is an unordered pair {x, y} of distinct positions; C_b the cells co-blocked at scale b; blocks {(i−1)b+1,…,ib} ∩ [n] → Cell = Sym2 (Pos d m); coBlocked π b = non-diagonal s(x,y) with π x / b = π y / b (0-based ranks and labels); reason: same cells and same blocks after the 0-based shift
--   - encoding: probability over the uniform input → prob d m E = (PMF.uniformOfFintype (Input d m)).toOuterMeasure {π | E π}; reason: the uniform distribution on the n! bijections
--   - encoding: log n (base 2) → Real.logb 2 (nR d m); reason: the paper fixes base 2 (p. 8); n ≥ 2 so the logarithm is positive
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Lemma 3.4, p. 11

import Definitions.Def_MovementSorting_Exponent_Geometry

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Lemma 3.4 (p. 11): fix `α < 1`. There is `c = c(d, α)` such that for sufficiently large `n`,
with probability at least `1 - n^{-10}` over the uniform input, for every dyadic scale
`b = 2^i ≤ n^α`, every route of movement `L` visits at most `c(1 + L(b/n)^{1/D}) log n` cells of
`C_b`. -/
theorem lemma_3_4 :
    ∀ d : ℕ, 1 ≤ d → ∀ α : ℝ, α < 1 → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ m : ℕ, 2 ≤ m → n₀ ≤ m ^ d →
        ENNReal.ofReal (1 - nR d m ^ (-10 : ℝ)) ≤ prob d m (fun π =>
          ∀ i : ℕ, ((2 ^ i : ℕ) : ℝ) ≤ nR d m ^ α →
            ∀ ρ : List (Config d m), IsRoute ρ →
              (visitedCount ρ (coBlocked π (2 ^ i)) : ℝ) ≤
                c * (1 + (movement ρ : ℝ) * (((2 ^ i : ℕ) : ℝ) / nR d m) ^ (1 / (2 * d : ℝ))) *
                  Real.logb 2 (nR d m)) := by sorry

end MovementSorting.Exponent
