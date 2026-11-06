-- Prove2me | Theorems.Thm_HOTrap_lemma_3_9
-- name    : HOTrap.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:48:28.722+00:00
-- url     : https://prove2.me/theorems/02f3853d-9318-476c-b054-c2404ae24d57
-- title:
--   Lemma 3.9 — stationarity from an approximate model
-- statement:
--   Let $R\subseteq\mathbb R^d$ be nonempty, compact and convex, let $x\in R$ and $\varepsilon>0$. Suppose that $f$ and $P$ are continuously differentiable on a neighbourhood of $R$ with $\|\nabla P-\nabla f\|_{\infty,R}\le\varepsilon/8$, and let $\Psi(y)=P(y)-P(x)+\frac{3\varepsilon}4\|y-x\|_2$. Every minimizer $z$ of $\Psi$ over $R$ has the following properties.
--
--   1. If every point of $\partial R$ is $(\varepsilon/2)$-unreachable from $x$, then $z\in\mathrm{int}(R)$ and $\|\nabla f(z)\|_2\le\varepsilon$.
--   2. If $R\subseteq[0,1]^d$ and every point of $\partial_{[0,1]^d}R$ is $(\varepsilon/2)$-unreachable from $x$, then $z\in\mathrm{int}_{[0,1]^d}(R)$ and $\|G_\gamma(z)\|_2\le\varepsilon$ for every $\gamma>0$.
--
--   This lemma converts a trapped region and a gradient-accurate scalar model into the point the algorithm returns, without a $C^{1,1}$ assumption.
--
--   **Formalization Note** $\partial R$ is `frontier R`.
--
--   Differences from the source:
--   - generalization: d ≥ 2, fixed in Section 3 → any d; reason: the proof does not use d ≥ 2; d ≥ 2 is the instance used
--   - encoding: "on a neighborhood of S" → an open set U containing S; reason: the standard meaning of the phrase
--   - encoding: ∥∇P − ∇f∥ in the sup norm over R is at most ε/8 → a pointwise bound on R; reason: the same statement
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma 3.9, p.17

import Mathlib
import Definitions.Def_HOTrap_CkNear
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_HOTrap_projGrad
import Definitions.Def_HOTrap_Unreachable
import Definitions.Def_HOTrap_cubeInterior
import Definitions.Def_HOTrap_cubeBoundary
import Definitions.Def_HOTrap_penalizedModel

namespace HOTrap

/-- **Lemma 3.9 (stationarity from an approximate model).** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma 3.9, p.17. Let `R ⊆ ℝ^d` be nonempty,
compact and convex, `x ∈ R` and `ε > 0`. Suppose `f` and `P` are `C¹` near `R` with `∥∇P − ∇f∥_{∞,R} ≤ ε/8`. Every
minimizer `z` over `R` of `Ψ` in (4) satisfies: (1) if every point of `∂R` is `(ε/2)`-unreachable from `x`, then
`z ∈ int(R)` and `∥∇f(z)∥₂ ≤ ε`; (2) if `R ⊆ [0,1]^d` and every point of `∂_{[0,1]^d}R` is `(ε/2)`-unreachable from
`x`, then `z ∈ int_{[0,1]^d}(R)` and `∥G_γ(z)∥₂ ≤ ε` for every `γ > 0`.

**Formalization Note** `∂R` is `frontier R`, which equals `R \ interior R` because `R` is closed. -/
theorem lemma_3_9 {d : ℕ} (R : Set (EuclideanSpace ℝ (Fin d))) (hRne : R.Nonempty) (hRc : IsCompact R)
    (hRv : Convex ℝ R) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ R) (ε : ℝ) (hε : 0 < ε) (f P : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : CkNear R 1 f) (hP : CkNear R 1 P)
    (hgrad : ∀ y ∈ R, ‖gradient P y - gradient f y‖ ≤ ε / 8) (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ R)
    (hmin : ∀ y ∈ R, penalizedModel P x ε z ≤ penalizedModel P x ε y) :
    ((∀ y ∈ frontier R, Unreachable f x (ε / 2) y) → z ∈ interior R ∧ ‖gradient f z‖ ≤ ε) ∧
    (R ⊆ GeomDRSub.cube d → (∀ y ∈ cubeBoundary R, Unreachable f x (ε / 2) y) →
      z ∈ cubeInterior R ∧ ∀ γ : ℝ, 0 < γ → ‖projGrad f γ z‖ ≤ ε) := by sorry

end HOTrap
