-- Prove2me | Theorems.Thm_HuberSNSDP_multiplier_unique
-- name    : HuberSNSDP.multiplier_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:22.416985+00:00
-- url     : https://prove2.me/theorems/e352e01c-4b54-40da-b05e-069e1db34bbb
-- title:
--   p.8 ([1, Theorem 2]) — primal nondegeneracy at an optimal $\bar X$ makes $\mathcal M(\bar X)$ a singleton
-- statement:
--   Let $\bar X$ be an optimal solution of the primal SDP (1) at which primal constraint nondegeneracy (9) holds. Then the multiplier set
--   $$\mathcal M(\bar X)=\{(y,Z)\in\mathbb R^m\times\mathbb S^n:(\bar X,y,Z)\text{ is a KKT point}\}$$
--   is a singleton.
--
--   This puts Lemma 2 in force at the limit point in the proof of Proposition 2.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: the standing assumption of p.2 (an optimal solution of (1) exists and Slater's condition holds), stated once for the whole paper → the explicit hypothesis `D.Standing`; reason: the paper assumes it throughout ("In this paper, we assume", p.2)
--   - encoding: "$\mathcal M(\bar X)$ is a singleton" → `∃! p, p ∈ D.mult X̄`; reason: a singleton is a set with exactly one element; nonemptiness holds under the standing assumption (p.2)
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, p.8, "M(X̄) is a singleton [1, Theorem 2]"

import Mathlib
import Definitions.Def_HuberSNSDP_Setting

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- p.8 (Liang, Sun & Toh, arXiv:2303.05825v4; cited from [1, Theorem 2]): "if `X̄` is an optimal
solution for (1), then under the primal constraint nondegeneracy condition, we can show that
`M(X̄)` is a singleton".

**Formalization Note.** "Singleton" is `∃!`: `M(X̄)` is nonempty (p.2, under the standing
assumption, which is a hypothesis) and has at most one element. -/
theorem multiplier_unique {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (Xbar : SymMat (Fin n))
    (hopt : D.PrimalOptimal Xbar) (hP : D.PrimalNondeg Xbar) :
    ∃! p : EuclideanSpace ℝ (Fin m) × SymMat (Fin n), p ∈ D.mult Xbar := by sorry

end HuberSNSDP
