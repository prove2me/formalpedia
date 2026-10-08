-- Prove2me | Theorems.Thm_MifflinSemismooth_Optimality_exists_convex_combination_zero
-- name    : MifflinSemismooth.Optimality.exists_convex_combination_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:05.824023+00:00
-- url     : https://prove2.me/theorems/5b2cf1ad-900e-45d2-b1fa-7fb99c8d97c1
-- title:
--   Proof of Theorem 9, p. 20 — h(x̄) = 0 and 0 ∈ M(x̄) give λ ∈ [0,1], ḡ ∈ ∂f(x̄), ĝ ∈ ∂h(x̄) with λḡ + (1−λ)ĝ = 0
-- statement:
--   Let $f,h:\mathbb R^n\to\mathbb R$ both be Lipschitz on a ball about $\bar x$, suppose $h(\bar x)=0$ and $0\in M(\bar x)=\operatorname{conv}\{\partial f(\bar x)\cup\partial h(\bar x)\}$. Then there exist $\lambda\in[0,1]$, $\bar g\in\partial f(\bar x)$ and $\hat g\in\partial h(\bar x)$ such that
--   $$
--   \lambda\bar g+(1-\lambda)\hat g=0.
--   $$
--
--   This rewrites the stationarity condition on the boundary of the feasible set as a Fritz John type multiplier condition, which the rest of the proof of Theorem 9 splits into the cases $\lambda=0$ and $\lambda>0$.
--
--   **Formalization Note** The two Lipschitz hypotheses are the part of the semiconvexity hypothesis of Theorem 9 that this step uses: they make $\partial f(\bar x)$ and $\partial h(\bar x)$ nonempty (Proposition 1(a)). Without them, $0\in\operatorname{conv}(\partial f\cup\partial h)$ with $\partial h(\bar x)=\emptyset$ would not produce $\hat g$.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 20, §5, proof of Theorem 9, case h(x̄) = 0

import Mathlib
import Definitions.Def_MifflinSemismooth_Optimality_Setting

namespace MifflinSemismooth.Optimality

/-- Mifflin (1976), §5, proof of Theorem 9, p. 20: if `h(x̄) = 0` and `0 ∈ M(x̄)`, there exist
`λ ∈ [0, 1]`, `ḡ ∈ ∂f(x̄)` and `ĝ ∈ ∂h(x̄)` with `λ ḡ + (1 - λ) ĝ = 0`. -/
theorem exists_convex_combination_zero {n : ℕ} (f h : EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) (hf : MifflinSemismooth.Extremal.LipschitzNear f xbar) (hh : MifflinSemismooth.Extremal.LipschitzNear h xbar)
    (hzero : h xbar = 0) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Mmap f h xbar) :
    ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∃ gbar ∈ MifflinSemismooth.Extremal.genGrad f xbar, ∃ ghat ∈ MifflinSemismooth.Extremal.genGrad h xbar,
      lam • gbar + (1 - lam) • ghat = 0 := by sorry

end MifflinSemismooth.Optimality
