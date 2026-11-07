-- Prove2me | Theorems.Thm_FriedgutCoalition_theorem_3_1
-- name    : FriedgutCoalition.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:22.608881+00:00
-- url     : https://prove2.me/theorems/c5128e6b-c406-4aef-8d0a-6d38a6e2fd5d
-- title:
--   Theorem 3.1 — every $f:[r]^n\to\{0,1\}$ has a coalition of $O_\varepsilon(n/\sqrt{\log n})$ coordinates forcing some output
-- statement:
--   For every $\varepsilon>0$ there is a constant $C=C(\varepsilon)>0$ such that for all $r,n\in\mathbb N$ and every function $f:[r]^n\to\{0,1\}$ there are $b\in\{0,1\}$ and $B\subseteq[n]$ with
--
--   $$|B|\le C\cdot\frac{n}{\sqrt{\log n}}\qquad\text{and}\qquad\mathbf P^b_B(f)\ge1-\varepsilon,$$
--
--   where $[r]^n$ carries the uniform distribution and the coalition $B$ chooses its values after the other coordinates are drawn. Logarithms are base $2$.
--
--   The constant does not depend on the alphabet size $r$. This is the finite-alphabet form of the paper's main result, and Corollary 3.2 is derived from it.
--
--   Differences from the source:
--   - encoding: |B| ≤ C · n/√log(n) → |B| · √(log₂ n) ≤ C · n; reason: the same inequality for n ≥ 2; at n = 1 the printed bound divides by zero and the Lean form puts no bound on |B| (Lean's x/0 = 0 would instead force |B| ≤ 0, which is false); logarithms are base 2 (p.4)
--   - encoding: r ∈ ℕ → r ≥ 1 (0 < r); reason: [0]ⁿ is empty for n ≥ 1 and carries no uniform distribution; with Lean's empty sums every probability would be 0
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Theorem 3.1, p.8

import Mathlib
import Definitions.Def_FriedgutCoalition_coalProb

namespace FriedgutCoalition

/-- **Theorem 3.1** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.8). For every `ε > 0` there is
`C = C(ε) > 0` such that for all `r, n ∈ ℕ` and every `f : [r]ⁿ → {0,1}` there are `b ∈ {0,1}` and
`B ⊆ [n]` with `|B| ≤ C · n / √(log n)` and `P^b_B(f) ≥ 1 − ε` (uniform distribution on `[r]ⁿ`).

**Formalization Note.**
* `|B| ≤ C · n / √(log₂ n)` is written `|B| · √(log₂ n) ≤ C · n` (the same for `n ≥ 2`; no bound at
  `n = 1`, where the printed bound divides by zero).
* `[r] = {1, …, r}` is `Fin r`, and `0 < r` is assumed: `[0]ⁿ` carries no uniform distribution.
* `f` is arbitrary (not assumed monotone); `C` comes before `r`, `n` and `f`. -/
theorem theorem_3_1 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (r n : ℕ), 0 < r → ∀ f : (Fin n → Fin r) → Bool,
      ∃ (b : Bool) (B : Finset (Fin n)),
        (B.card : ℝ) * Real.sqrt (Real.logb 2 n) ≤ C * n ∧
          1 - ε ≤ coalProb (unif r) f B b := by sorry

end FriedgutCoalition
