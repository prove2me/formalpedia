-- Prove2me | Theorems.Thm_GrothendieckLB_eq_38
-- name    : GrothendieckLB.eq_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:56.663585+00:00
-- url     : https://prove2.me/theorems/4abe1684-354e-462c-8f73-18975d0092bb
-- title:
--   Eq. (38): the fiber reduction $\|P_3k\|^2\le\mathbb E_T V(u_T)$
-- statement:
--   Let $k:\mathbb R\times\mathbb R^n\to\{-1,0,1\}$ be measurable, and for $t\in\mathbb R^n$ let $u_t(s):=k(s,t)$ be its fiber over $t$. With $T\sim N(0,I_n)$,
--   $$
--   \|P_3k\|^2\le\mathbb E_T\,V(u_T).
--   $$
--   This reduces the disagreement term to a one-dimensional quantity, the source of the dimension-free bounds that follow.
--
--   Differences from the source:
--   - generalization: h, k built from odd sign functions (Part II introduction, p.30) → every measurable ternary function; reason: the argument uses only the values of the function; each ternary function is the part of a sign pair, and the odd case is a specialization
--   - encoding: S is the direction of P₁h (Section 8.2, p.33) → S is the first coordinate of ℝⁿ⁺¹ and k is arbitrary; reason: ‖P₃k‖² is rotation invariant and rotating a ternary k gives a ternary k, so every orthonormal split is covered
--   - encoding: P₁, P₃ as orthogonal projections in L² → moment sums p1Inner, p3Inner; reason: the moments are the coordinates of the projections in the orthonormal Hermite basis
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (38), p.36

import Mathlib
import Definitions.Def_GrothendieckLB_IsTernaryFn
import Definitions.Def_GrothendieckLB_p3NormSq
import Definitions.Def_GrothendieckLB_gaussExp
import Definitions.Def_GrothendieckLB_V

namespace GrothendieckLB

/-- Eq. (38), the fiber reduction (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (38), p.36): for a measurable ternary `k` on
`ℝ^{n+1} = ℝ × ℝⁿ`, with fibers `u_t(s) := k(s, t)`, one has `‖P₃k‖² ≤ E_T[V(u_T)]`, `T ∼ N(0, I_n)`.

**Formalization Note** `S` is the first coordinate. The page takes `S` in the direction of `P₁h`;
since `k` is arbitrary and `‖P₃ · ‖²` is rotation invariant, the coordinate split is the general
case. -/
theorem eq_38 {n : ℕ} {k : (Fin (n + 1) → ℝ) → ℝ} (hk : IsTernaryFn k) :
    p3NormSq k ≤ gaussExp fun t : Fin n → ℝ => V fun s => k (Fin.cons s t) := by sorry

end GrothendieckLB
