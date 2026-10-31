-- Prove2me | Theorems.Thm_HuberSNSDP_eq_42
-- name    : HuberSNSDP.eq_42
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:15.537635+00:00
-- url     : https://prove2.me/theorems/a8fda711-59fc-43e9-bbfa-5691370265dc
-- title:
--   (42) — $\|\hat{\mathcal E}'(w)^{-1}\|=O(1)$ near a nondegenerate zero of $\hat{\mathcal E}$
-- statement:
--   Let $\kappa_p,\kappa_c>0$ and let $\bar w=(\bar\epsilon,\bar X,\bar y,\bar Z)$ satisfy $\hat{\mathcal E}(\bar w)=0$, with primal constraint nondegeneracy at $\bar X$ and dual constraint nondegeneracy at $(\bar y,\bar Z)$. Then there are a neighbourhood $U$ of $\bar w$ and a constant $c$ such that at every $w\in U$ with $\epsilon>0$ the derivative $\hat{\mathcal E}'(w)$ is invertible and
--   $$\|\hat{\mathcal E}'(w)^{-1}\|\le c .$$
--
--   In the proof of Theorem 3 this is the bound $\|\hat{\mathcal E}'(\epsilon^k,X^k,y^k,Z^k)^{-1}\|=O(1)$ (42) along the iterates.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: the standing assumption of p.2 (an optimal solution of (1) exists and Slater's condition holds), stated once for the whole paper → the explicit hypothesis `D.Standing`; reason: the paper assumes it throughout ("In this paper, we assume", p.2)
--   - encoding: dual constraint nondegeneracy "at $(\bar y,\bar Z)$" → `DualNondeg D Z̄`, a condition on $\bar Z$ alone; reason: condition (10) involves only $\bar Z$; $\bar y$ is the dual variable of the same KKT point
--   - reading: (10): "a feasible solution $(\bar y,\bar Z)\in\mathbb R^n\times\mathbb S^n_+$" → $\bar y\in\mathbb R^m$; reason: $y$ is the dual variable of the $m$ constraints of (2); $\mathbb R^n$ is a misprint
--   - generalization: "for all $k$ sufficiently large, $\|\hat{\mathcal E}'(\epsilon^k,X^k,y^k,Z^k)^{-1}\|=O(1)$" along a run converging to $\bar w$ → a uniform bound on a neighbourhood of $\bar w$, at every point with $\epsilon>0$, for any zero $\bar w$ of $\hat{\mathcal E}$ with the two nondegeneracy conditions; reason: the iterates have $\epsilon^k>0$ and, along a subsequence converging to $\bar w$, eventually lie in the neighbourhood; the accumulation point is a zero of $\hat{\mathcal E}$ by Theorem 2
--   - encoding: $\|\hat{\mathcal E}'(w)^{-1}\|=O(1)$ → a two-sided continuous linear inverse of norm at most $c$; reason: the same statement in finite dimension
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, proof of Theorem 3, (42), p.45

import Mathlib
import Definitions.Def_HuberSNSDP_Algorithm

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Display (42), p.45, in the proof of Theorem 3 (Liang, Sun & Toh, arXiv:2303.05825v4):
under primal and dual constraint nondegeneracy at a solution `w̄ = (0, X̄, ȳ, Z̄)` of `ℰ̂ = 0`,
`‖ℰ̂′(εᵏ, Xᵏ, yᵏ, Zᵏ)⁻¹‖ = O(1)` near `w̄`.

Stated on a neighbourhood: there are a neighbourhood `U` of `w̄` and `c` such that at every
`w ∈ U` with `ε > 0`, `ℰ̂′(w)` has a two-sided continuous linear inverse of norm at most `c`.

**Formalization Note.** The page states the bound for the iterates of a run for `k` large; any
sequence converging to `w̄` with `εᵏ > 0` eventually lies in `U` (a generalization). -/
theorem eq_42 {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (kp kc : ℝ) (hkp : 0 < kp)
    (hkc : 0 < kc) (wbar : ISpace n m) (h0 : D.Ehat kp kc wbar = 0)
    (hP : D.PrimalNondeg (XOf wbar)) (hDu : D.DualNondeg (ZOf wbar)) :
    ∃ U ∈ 𝓝 wbar, ∃ c : ℝ, ∀ w ∈ U, 0 < epsOf w →
      ∃ Winv : EhatSpace n m →L[ℝ] ISpace n m,
        Winv.comp (fderiv ℝ (D.Ehat kp kc) w) = ContinuousLinearMap.id ℝ (ISpace n m) ∧
        (fderiv ℝ (D.Ehat kp kc) w).comp Winv = ContinuousLinearMap.id ℝ (EhatSpace n m) ∧
        ‖Winv‖ ≤ c := by sorry

end HuberSNSDP
