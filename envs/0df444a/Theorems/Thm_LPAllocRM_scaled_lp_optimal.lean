-- Prove2me | Theorems.Thm_LPAllocRM_scaled_lp_optimal
-- name    : LPAllocRM.scaled_lp_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:53.329977+00:00
-- url     : https://prove2.me/theorems/e25b1f9c-2c80-42ff-b77a-928cac28c18a
-- title:
--   $kx^*$ is optimal for the $k$th LP (6), with value $k\beta$
-- statement:
--   Let $x^*$ be an optimal solution of the linear program (3)
--
--   $$\max_x\{f\cdot x : Ax\le c,\ 0\le x\le\mu\},$$
--
--   and $\beta=f\cdot x^*$. Then for every $k=1,2,\dots$, the vector $kx^*$ is an optimal solution of the $k$th linear program (6)
--
--   $$\max_x\{f\cdot x : Ax\le kc,\ 0\le x\le k\mu\},$$
--
--   and the optimal objective value of (6) is $k\beta$: it is attained, and no feasible point of (6) has a larger objective value.
--
--   This identifies the deterministic benchmark of the scaled problems and is used in Lemma 2's upper bound $v^{(k)}\le k\beta$.
--
--   Differences from the source:
--   - generalization: the model's c > 0, a_ij ⩾ 0 and μ = ED(τ) ⩾ 0 → no condition on A, c or μ; reason: the scaling argument uses none of them; the Lean statement specializes to the paper's data
--   - encoding: problems k = 1, 2, … (k ⩾ 1) → k : ℕ+, limits along atTop on ℕ+; reason: same index set; there is no problem k = 0
--   - encoding: "the kth LP has optimal objective value kβ" → kβ is the greatest element of the set of objective values of feasible points of (6); reason: this is what an attained optimal value means
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, §4, claim after eq. (6), p.723

import Mathlib
import Definitions.Def_LPAllocRM_IsLPOptimal
open Matrix

namespace LPAllocRM

/-- If `x*` is an optimal solution of the LP (3) `max {f · x : A x ≤ c, 0 ≤ x ≤ μ}`, then for every
`k = 1, 2, …` the vector `k x*` is an optimal solution of the kth LP (6)
`max {f · x : A x ≤ k c, 0 ≤ x ≤ k μ}`, whose optimal objective value is `k β`, `β = f · x*`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
§4, claim after (6), p.723 (PDF p.4).

**Formalization Note** "The kth LP has optimal objective value kβ" is stated as: `k β` is the greatest
element of the set of objective values of feasible points of (6). No sign condition on `A`, `c` or
`μ` is needed and none is assumed. -/
theorem scaled_lp_optimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
    (μ : Fin n → ℝ) (f : Fin n → ℝ) (xstar : Fin n → ℝ) (hx : IsLPOptimal A c μ f xstar)
    (k : ℕ+) :
    IsLPOptimal A (((k : ℕ) : ℝ) • c) (((k : ℕ) : ℝ) • μ) f (((k : ℕ) : ℝ) • xstar) ∧
      IsGreatest {z : ℝ | ∃ y : Fin n → ℝ,
          LPFeasible A (((k : ℕ) : ℝ) • c) (((k : ℕ) : ℝ) • μ) y ∧ z = f ⬝ᵥ y}
        (((k : ℕ) : ℝ) * (f ⬝ᵥ xstar)) := by sorry

end LPAllocRM
