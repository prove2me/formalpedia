-- Prove2me | Theorems.Thm_HuberSNSDP_lemma_2
-- name    : HuberSNSDP.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:40.141684+00:00
-- url     : https://prove2.me/theorems/b433938b-a67b-409c-aa2c-4653e043a636
-- title:
--   Lemma 2 ([11, Proposition 15]) — when $\mathcal M(\bar X)=\{(\bar y,\bar Z)\}$, SSOSC $\Leftrightarrow$ dual nondegeneracy
-- statement:
--   Let $(\bar X,\bar y,\bar Z)$ be a KKT point of (1)–(2) with $\mathcal M(\bar X)=\{(\bar y,\bar Z)\}$. Then the strong second-order sufficient condition (Definition 3) holds at $\bar X$ if and only if dual constraint nondegeneracy (10) holds at $(\bar y,\bar Z)$.
--
--   The paper cites this from Chan and Sun; it converts dual nondegeneracy into the curvature condition used with Lemma 9.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: the standing assumption of p.2 (an optimal solution of (1) exists and Slater's condition holds), stated once for the whole paper → the explicit hypothesis `D.Standing`; reason: the paper assumes it throughout ("In this paper, we assume", p.2)
--   - encoding: dual constraint nondegeneracy "at $(\bar y,\bar Z)$" → `DualNondeg D Z̄`, a condition on $\bar Z$ alone; reason: condition (10) involves only $\bar Z$; $\bar y$ is the dual variable of the same KKT point
--   - reading: (10): "a feasible solution $(\bar y,\bar Z)\in\mathbb R^n\times\mathbb S^n_+$" → $\bar y\in\mathbb R^m$; reason: $y$ is the dual variable of the $m$ constraints of (2); $\mathbb R^n$ is a misprint
--   - encoding: $\sup_{(y,Z)\in\mathcal M(\bar X)}\{-\Gamma_{\bar X}(-Z,H)\}>0$ → some $(y,Z)\in\mathcal M(\bar X)$ has $-\Gamma_{\bar X}(-Z,H)>0$; reason: a supremum of real numbers is positive exactly when some element is
--   - reading: $\mathrm{app}(y,Z)$ uses $P_\beta,P_\gamma$ of "the" spectral decomposition of $\bar X-\bar Z$ → $P_\beta,P_\gamma$ from any spectral decomposition of $\bar X-Z$ for the given $(y,Z)$; reason: here $\mathcal M(\bar X)=\{(\bar y,\bar Z)\}$, so the two coincide, and the blocks $P_\beta^TBP_\gamma$, $P_\gamma^TBP_\gamma$ vanish independently of the choice of $P$
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Lemma 2, p.9 (cited [11, Proposition 15]); Definition 3, p.8

import Mathlib
import Definitions.Def_HuberSNSDP_Setting

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Lemma 2, p.9 (Liang, Sun & Toh, arXiv:2303.05825v4; cited from Chan–Sun [11, Proposition 15]).

Let `(X̄, ȳ, Z̄)` be a KKT point with `M(X̄) = {(ȳ, Z̄)}`. Then the strong second-order sufficient
condition (Definition 3) holds at `X̄` if and only if dual constraint nondegeneracy (10) holds at
`(ȳ, Z̄)`.

**Formalization Note.** The standing assumption of p.2 is a hypothesis. A KKT point's `X̄` is optimal
for (1), as Definition 3 requires. -/
theorem lemma_2 {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (Xbar : SymMat (Fin n))
    (ybar : EuclideanSpace ℝ (Fin m)) (Zbar : SymMat (Fin n)) (hK : D.KKT Xbar ybar Zbar)
    (hM : D.mult Xbar = {(ybar, Zbar)}) :
    D.SSOSC Xbar ↔ D.DualNondeg Zbar := by sorry

end HuberSNSDP
