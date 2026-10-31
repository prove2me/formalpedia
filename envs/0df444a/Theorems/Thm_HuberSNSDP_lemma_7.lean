-- Prove2me | Theorems.Thm_HuberSNSDP_lemma_7
-- name    : HuberSNSDP.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:18.263985+00:00
-- url     : https://prove2.me/theorems/4ab4290b-204f-488e-9e60-7cf908f0bac8
-- title:
--   Lemma 7 — a uniform Armijo step near every point with $\epsilon>0$
-- statement:
--   Fix the parameters of Algorithm 1 and $\delta=\sqrt2\max\{r\hat\epsilon,\hat\eta\}<1$. For any $(\epsilon',X',y',Z')\in\mathbb R_{++}\times\mathbb X$ there exist an open neighbourhood $\mathcal U$ of it and $\bar\alpha\in(0,1]$ such that for every $w=(\epsilon,X,y,Z)\in\mathcal U$ with $\epsilon>0$, every $\alpha\in(0,\bar\alpha]$ and every direction $\Delta=(\Delta\epsilon;\Delta X;\Delta y;\Delta Z)\in\mathbb R\times\mathbb X$ satisfying
--   $$\Delta\epsilon=-\epsilon+\zeta(w)\hat\epsilon,\qquad\|\mathcal E(w)+\mathcal E'(w)\Delta\|\le\hat\eta\|\hat{\mathcal E}(w)\|,$$
--   one has
--   $$\psi(w+\alpha\Delta)\le[1-2\sigma(1-\delta)\alpha]\,\psi(w).$$
--
--   This is what makes the line search of Algorithm 1 terminate after finitely many backtracking steps.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: the standing assumption of p.2 (an optimal solution of (1) exists and Slater's condition holds), stated once for the whole paper → the explicit hypothesis `D.Standing`; reason: the paper assumes it throughout ("In this paper, we assume", p.2)
--   - reading: "where $\Delta$ … satisfies" the two conditions → the inequality for every $\Delta$ satisfying them, with $\mathcal U$ and $\bar\alpha$ chosen before $w$, $\alpha$ and $\Delta$; reason: the lemma is applied to whatever direction the algorithm computed; the proof (Appendix F) bounds every such $\Delta$ uniformly on $\mathcal U$
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Lemma 7, p.14

import Mathlib
import Definitions.Def_HuberSNSDP_Algorithm

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Lemma 7, p.14 (Liang, Sun & Toh, arXiv:2303.05825v4).

For any `(ε′, X′, y′, Z′) ∈ ℝ₊₊ × 𝕏` there exist an open neighbourhood `𝒰` of it and `ᾱ ∈ (0, 1]`
such that for every `(ε, X, y, Z) ∈ 𝒰` with `ε > 0` and every `α ∈ (0, ᾱ]`,
`ψ(w + αΔ) ≤ [1 − 2σ(1 − δ)α] ψ(w)`, for every `Δ = (Δε; ΔX; Δy; ΔZ) ∈ ℝ × 𝕏` with
`Δε = −ε + ζ(w)ε̂` and `‖ℰ(w) + ℰ′(w)Δ‖ ≤ η̂‖ℰ̂(w)‖`.

**Formalization Note.** `𝒰` and `ᾱ` are chosen before `w`, `α` and `Δ`; the constants are those of
Algorithm 1 (`Params`). -/
theorem lemma_7 {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (θ : Params) (w' : ISpace n m)
    (hw' : 0 < epsOf w') :
    ∃ U : Set (ISpace n m), IsOpen U ∧ w' ∈ U ∧ ∃ αbar : ℝ, 0 < αbar ∧ αbar ≤ 1 ∧
      ∀ w ∈ U, 0 < epsOf w → ∀ α : ℝ, 0 < α → α ≤ αbar → ∀ Δ : ISpace n m,
        epsOf Δ = -epsOf w + zeta D θ w * θ.epsHat →
        ‖D.Emap θ.kp θ.kc w + fderiv ℝ (D.Emap θ.kp θ.kc) w Δ‖ ≤
            θ.etaHat * ‖D.Ehat θ.kp θ.kc w‖ →
          psi D θ (w + α • Δ) ≤ (1 - 2 * θ.sigma * (1 - θ.delta) * α) * psi D θ w := by sorry

end HuberSNSDP
