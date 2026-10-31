-- Prove2me | Theorems.Thm_HuberSNSDP_proposition_2
-- name    : HuberSNSDP.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:14.430444+00:00
-- url     : https://prove2.me/theorems/4f38fd8c-c426-47c3-a548-391c9ca458ed
-- title:
--   Proposition 2 — at a zero of $\hat{\mathcal E}$: nondegeneracy $\Leftrightarrow$ $\partial_B\hat{\mathcal E}$ nonsingular $\Leftrightarrow$ $\partial\hat{\mathcal E}$ nonsingular
-- statement:
--   Let $\kappa_p,\kappa_c>0$ and let $(\bar\epsilon,\bar X,\bar y,\bar Z)$ satisfy $\hat{\mathcal E}(\bar\epsilon,\bar X,\bar y,\bar Z)=0$. The following are equivalent:
--
--   1. primal constraint nondegeneracy holds at $\bar X$ and dual constraint nondegeneracy holds at $(\bar y,\bar Z)$;
--   2. every element of $\partial_B\hat{\mathcal E}(\bar\epsilon,\bar X,\bar y,\bar Z)$ is nonsingular;
--   3. every element of $\partial\hat{\mathcal E}(\bar\epsilon,\bar X,\bar y,\bar Z)$ is nonsingular.
--
--   This is the regularity statement behind the superlinear rate of Theorem 3.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: the standing assumption of p.2 (an optimal solution of (1) exists and Slater's condition holds), stated once for the whole paper → the explicit hypothesis `D.Standing`; reason: the paper assumes it throughout ("In this paper, we assume", p.2)
--   - encoding: a linear map is nonsingular → `Function.Bijective` of the continuous linear map; reason: finite-dimensional spaces of equal dimension; same meaning
--   - encoding: dual constraint nondegeneracy "at $(\bar y,\bar Z)$" → `DualNondeg D Z̄`, a condition on $\bar Z$ alone; reason: condition (10) involves only $\bar Z$; $\bar y$ is the dual variable of the same KKT point
--   - reading: (10): "a feasible solution $(\bar y,\bar Z)\in\mathbb R^n\times\mathbb S^n_+$" → $\bar y\in\mathbb R^m$; reason: $y$ is the dual variable of the $m$ constraints of (2); $\mathbb R^n$ is a misprint
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Proposition 2, p.15 (proof: Appendix J)

import Mathlib
import Definitions.Def_HuberSNSDP_Algorithm

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Proposition 2, p.15 (Liang, Sun & Toh, arXiv:2303.05825v4).

Let `(ε̄, X̄, ȳ, Z̄)` satisfy `ℰ̂(ε̄, X̄, ȳ, Z̄) = 0`. The following are equivalent:
1. primal constraint nondegeneracy holds at `X̄` and dual constraint nondegeneracy at `(ȳ, Z̄)`;
2. every element of `∂_Bℰ̂(ε̄, X̄, ȳ, Z̄)` is nonsingular;
3. every element of `∂ℰ̂(ε̄, X̄, ȳ, Z̄)` is nonsingular.

**Formalization Note.** `ℰ̂` is (19) with constants `κp, κc > 0`; "nonsingular" is bijectivity; the
standing assumption of p.2 is a hypothesis. -/
theorem proposition_2 {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (kp kc : ℝ) (hkp : 0 < kp)
    (hkc : 0 < kc) (wbar : ISpace n m) (h0 : D.Ehat kp kc wbar = 0) :
    List.TFAE
      [D.PrimalNondeg (XOf wbar) ∧ D.DualNondeg (ZOf wbar),
       ∀ V ∈ bJac (D.Ehat kp kc) wbar, Function.Bijective V,
       ∀ V ∈ clarkeJac (D.Ehat kp kc) wbar, Function.Bijective V] := by sorry

end HuberSNSDP
