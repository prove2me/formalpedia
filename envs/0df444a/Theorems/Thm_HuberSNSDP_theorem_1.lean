-- Prove2me | Theorems.Thm_HuberSNSDP_theorem_1
-- name    : HuberSNSDP.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:33.028623+00:00
-- url     : https://prove2.me/theorems/82192a7b-b51d-45b6-b4a9-4224593d6679
-- title:
--   Theorem 1 ([11, Theorem 18]) — nondegeneracy $\Leftrightarrow$ $\partial\mathcal F$ nonsingular $\Leftrightarrow$ $\partial_B\mathcal F$ nonsingular
-- statement:
--   Let $(\bar X,\bar y,\bar Z)\in\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ be a KKT point of (1)–(2) and $\mathcal F$ the KKT map (5). The following are equivalent:
--
--   1. primal constraint nondegeneracy (9) holds at $\bar X$ and dual constraint nondegeneracy (10) holds at $(\bar y,\bar Z)$;
--   2. every element of $\partial\mathcal F(\bar X,\bar y,\bar Z)$ is nonsingular;
--   3. every element of $\partial_B\mathcal F(\bar X,\bar y,\bar Z)$ is nonsingular.
--
--   The paper cites this from Chan and Sun; it is the template for Proposition 2.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: the standing assumption of p.2 (an optimal solution of (1) exists and Slater's condition holds), stated once for the whole paper → the explicit hypothesis `D.Standing`; reason: the paper assumes it throughout ("In this paper, we assume", p.2)
--   - encoding: a linear map is nonsingular → `Function.Bijective` of the continuous linear map; reason: finite-dimensional spaces of equal dimension; same meaning
--   - encoding: dual constraint nondegeneracy "at $(\bar y,\bar Z)$" → `DualNondeg D Z̄`, a condition on $\bar Z$ alone; reason: condition (10) involves only $\bar Z$; $\bar y$ is the dual variable of the same KKT point
--   - reading: (10): "a feasible solution $(\bar y,\bar Z)\in\mathbb R^n\times\mathbb S^n_+$" → $\bar y\in\mathbb R^m$; reason: $y$ is the dual variable of the $m$ constraints of (2); $\mathbb R^n$ is a misprint
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Theorem 1, p.8 (cited [11, Theorem 18])

import Mathlib
import Definitions.Def_HuberSNSDP_Setting

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Theorem 1, p.8 (Liang, Sun & Toh, arXiv:2303.05825v4; cited from Chan–Sun [11, Theorem 18]).

Let `(X̄, ȳ, Z̄)` be a KKT point. The following are equivalent:
1. primal constraint nondegeneracy (9) holds at `X̄` and dual constraint nondegeneracy (10) holds
   at `(ȳ, Z̄)`;
2. every element of `∂F(X̄, ȳ, Z̄)` is nonsingular;
3. every element of `∂_BF(X̄, ȳ, Z̄)` is nonsingular.

**Formalization Note.** `F` is (5) on `𝕏 = Sⁿ × ℝᵐ × Sⁿ`, with the published metric projector;
"nonsingular" is bijectivity; the standing assumption of p.2 is a hypothesis. -/
theorem theorem_1 {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (Xbar : SymMat (Fin n))
    (ybar : EuclideanSpace ℝ (Fin m)) (Zbar : SymMat (Fin n)) (hK : D.KKT Xbar ybar Zbar) :
    List.TFAE
      [D.PrimalNondeg Xbar ∧ D.DualNondeg Zbar,
       ∀ V ∈ clarkeJac D.Fmap (xPt Xbar ybar Zbar), Function.Bijective V,
       ∀ V ∈ bJac D.Fmap (xPt Xbar ybar Zbar), Function.Bijective V] := by sorry

end HuberSNSDP
