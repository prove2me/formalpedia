-- Prove2me | Theorems.Thm_HuberSNSDP_lemma_8
-- name    : HuberSNSDP.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:04.809972+00:00
-- url     : https://prove2.me/theorems/4236c853-ad97-457d-8e45-2fc57bbf151a
-- title:
--   Lemma 8 — an Armijo step keeps the iterate in $\mathcal N$
-- statement:
--   Let $w=(\epsilon,X,y,Z)$ with $\epsilon>0$ and $w\in\mathcal N=\{\epsilon\ge\zeta\hat\epsilon\}$, and let $\Delta$ have $\epsilon$-component $\Delta\epsilon=-\epsilon+\zeta(w)\hat\epsilon$. Then for every $\alpha\in[0,1]$ with
--   $$\psi(w+\alpha\Delta)\le[1-2\sigma(1-\delta)\alpha]\,\psi(w)$$
--   one has $w+\alpha\Delta\in\mathcal N$.
--
--   Together with Lemma 7 this keeps every iterate of Algorithm 1 in $\mathcal N$ with $\epsilon^k>0$.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: the standing assumption of p.2 (an optimal solution of (1) exists and Slater's condition holds), stated once for the whole paper → the explicit hypothesis `D.Standing`; reason: the paper assumes it throughout ("In this paper, we assume", p.2)
--   - generalization: the $k$-th iterate $(\epsilon^k,X^k,y^k,Z^k)$ and its direction $(\Delta\epsilon^k,\Delta X^k,\Delta y^k,\Delta Z^k)$ → any point $w$ with $\epsilon>0$, $w\in\mathcal N$, and any $\Delta$ with $\Delta\epsilon=-\epsilon+\zeta(w)\hat\epsilon$; reason: the iterate and its direction satisfy these hypotheses, so the statement specializes to the paper's; the proof (Appendix G) uses nothing else about them
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Lemma 8, p.14

import Mathlib
import Definitions.Def_HuberSNSDP_Algorithm

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Lemma 8, p.14 (Liang, Sun & Toh, arXiv:2303.05825v4).

Let `w = (ε, X, y, Z)` with `ε > 0` and `w ∈ 𝒩`, and let `Δ` have `ε`-component
`Δε = −ε + ζ(w)ε̂`. Then for any `α ∈ [0, 1]` with `ψ(w + αΔ) ≤ [1 − 2σ(1 − δ)α] ψ(w)`,
`w + αΔ ∈ 𝒩`.

**Formalization Note.** The paper states this for the `k`-th iterate and its direction `Δᵏ`; here
`w` and `Δ` are arbitrary with the stated properties (a generalization: the iterate and its
direction are instances). -/
theorem lemma_8 {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (θ : Params) (w Δ : ISpace n m)
    (hε : 0 < epsOf w) (hN : w ∈ NSet D θ)
    (hΔ : epsOf Δ = -epsOf w + zeta D θ w * θ.epsHat) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (harm : psi D θ (w + α • Δ) ≤ (1 - 2 * θ.sigma * (1 - θ.delta) * α) * psi D θ w) :
    w + α • Δ ∈ NSet D θ := by sorry

end HuberSNSDP
