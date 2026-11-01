-- Prove2me | Theorems.Thm_MarkovSA_proposition_A_1
-- name    : MarkovSA.proposition_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:03.392407+00:00
-- url     : https://prove2.me/theorems/175c2746-66d8-4431-9b2d-1401ee963bc4
-- title:
--   Proposition A.1 — the generalized Moreau envelope is convex, $(L/\theta)$-smooth and half a squared norm
-- statement:
--   Let $\|\cdot\|_s$ be an $L$-smooth norm on $E$ with $\ell_{cs}\|\cdot\|_s\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$ ($\ell_{cs},u_{cs}>0$), let $\theta>0$, and let
--
--   $$
--   M(x)=\min_{u\in E}\Big\{\tfrac12\|u\|_c^2+\tfrac1{2\theta}\|x-u\|_s^2\Big\}.
--   $$
--
--   Then:
--
--   1. $M$ is convex, differentiable, and $(L/\theta)$-smooth with respect to $\|\cdot\|_s$:
--   $$
--   M(y)\le M(x)+\langle\nabla M(x),y-x\rangle+\frac L{2\theta}\|x-y\|_s^2\qquad\text{for all }x,y;
--   $$
--   2. there is a norm $\|\cdot\|_m$ on $E$ with $M(x)=\frac12\|x\|_m^2$;
--   3. with $\ell_{cm}=(1+\theta\ell_{cs}^2)^{1/2}$ and $u_{cm}=(1+\theta u_{cs}^2)^{1/2}$, $\ \ell_{cm}\|\cdot\|_m\le\|\cdot\|_c\le u_{cm}\|\cdot\|_m$.
--
--   These properties make $M$ a Lyapunov function for a contraction in an arbitrary, possibly nonsmooth, norm.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with an arbitrary norm $\|\cdot\|_c$ → a finite-dimensional real normed space $E$ with its norm; reason: the same spaces up to linear isometry; $d$ does not appear in the statement
--   - encoding: $\langle\nabla M(x),v\rangle$ → the Fréchet derivative of $M$ at $x$ applied to $v$; reason: Lean's derivative; same value
--   - reading: $M$ is '$L/\theta$-smooth' → $M$ is differentiable and satisfies the displayed inequality; reason: the inequality uses $\nabla M$, so smoothness includes differentiability
--   - encoding: $M(x)=\min_u\{\dots\}$ → the infimum of the same objective; reason: the objective is nonnegative and the minimum is attained; same value
--   - encoding: 'a norm $\|\cdot\|_m$' → a function with the norm axioms; reason: same objects
--   - generalization: $\theta>0$ chosen with $\beta^2<(1+\theta\ell_{cs}^2)/(1+\theta u_{cs}^2)$ → any $\theta>0$; reason: the proposition does not involve $\beta$; the source's $\theta$ is a special case
--   - reading: $\ell_{cs}\|\cdot\|_c\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$ (as printed, p.24) → $\ell_{cs}\|\cdot\|_s\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$; reason: the left norm is a misprint: read literally it only says $\ell_{cs}\le1$, while pp.30 and 34 use $\|\cdot\|_s\le\|\cdot\|_c/\ell_{cs}$
--   - encoding: the norm $\|\cdot\|_s$ → a function with the norm axioms; reason: same objects
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Proposition A.1, p.25

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_MarkovSA_IsNormFun
import Definitions.Def_MarkovSA_IsSmoothNorm
import Definitions.Def_MarkovSA_moreauM
open MeasureTheory

namespace MarkovSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴]

/-- **Proposition A.1** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §A.1.1, p.25). Let `M(x) = min_u {½‖u‖_c² + (1/θ)·½‖x − u‖_s²}` be the
generalized Moreau envelope, where `‖·‖_s` is an `L`-smooth norm with `ℓ_cs‖·‖_s ≤ ‖·‖_c ≤ u_cs‖·‖_s` and `θ > 0`. Then
(1) `M` is convex and `(L/θ)`-smooth with respect to `‖·‖_s`: `M(y) ≤ M(x) + ⟨∇M(x), y − x⟩ + (L/2θ)‖x − y‖_s²`;
(2) there is a norm `‖·‖_m` with `M(x) = ½‖x‖_m²`;
(3) with `ℓ_cm = (1 + θℓ_cs²)^{1/2}`, `u_cm = (1 + θu_cs²)^{1/2}`, `ℓ_cm‖·‖_m ≤ ‖·‖_c ≤ u_cm‖·‖_m`.

**Formalization Note.** `‖·‖_c` is the norm of `E`; `⟨∇M(x), v⟩` is `fderiv ℝ M x v`, and part (1) includes
that `M` is differentiable, since the inequality uses its gradient. The norm of (2) is a function with the
norm axioms (`IsNormFun`). -/
theorem proposition_A_1 (s : E → ℝ) (L ℓ u θ : ℝ) (hs : IsSmoothNorm s L) (hℓ : 0 < ℓ) (hu : 0 < u)
    (hcmp : ∀ x, ℓ * s x ≤ ‖x‖ ∧ ‖x‖ ≤ u * s x) (hθ : 0 < θ) :
    (ConvexOn ℝ Set.univ (moreauM s θ) ∧ Differentiable ℝ (moreauM s θ) ∧
      ∀ x y : E, moreauM s θ y ≤
        moreauM s θ x + fderiv ℝ (moreauM s θ) x (y - x) + L / (2 * θ) * s (x - y) ^ 2) ∧
    ∃ m : E → ℝ, IsNormFun m ∧ (∀ x, moreauM s θ x = (1 / 2 : ℝ) * m x ^ 2) ∧
      ∀ x, Real.sqrt (1 + θ * ℓ ^ 2) * m x ≤ ‖x‖ ∧ ‖x‖ ≤ Real.sqrt (1 + θ * u ^ 2) * m x := by sorry

end MarkovSA
