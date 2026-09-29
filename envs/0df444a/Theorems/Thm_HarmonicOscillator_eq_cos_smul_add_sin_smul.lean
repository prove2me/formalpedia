-- Prove2me | Theorems.Thm_HarmonicOscillator_eq_cos_smul_add_sin_smul
-- name    : HarmonicOscillator.eq_cos_smul_add_sin_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T00:45:17.60098+00:00
-- url     : https://prove2.me/theorems/7cd64164-e0df-4d28-90b5-dd3e8c77bd5f
-- title:
--   Every solution of $g''+\alpha^2g=0$ is $\cos(\alpha t)v_1+\sin(\alpha t)v_2$
-- statement:
--   Let $E$ be a real inner product space, $\alpha\ne0$, and let $g:\mathbb R\to E$ be twice differentiable with
--
--   $$
--   g''(t)=-\alpha^2\,g(t)\qquad\text{for all }t\in\mathbb R .
--   $$
--
--   Then $g$ is determined by its value and velocity at the origin:
--
--   $$
--   g(t)=\cos(\alpha t)\,g(0)+\frac{\sin(\alpha t)}{\alpha}\,g'(0).
--   $$
--
--   **Role.** This is the vector-valued harmonic oscillator: the complete solution of the only second-order linear ODE that appears in the local analysis of homogeneous harmonic maps. Writing a homogeneous map of order $\alpha$ in polar coordinates as $w(r,\theta)=r^\alpha g(\theta)$ turns the harmonic map equation into exactly $g''+\alpha^2 g=0$, and this theorem is what converts that differential relation into the closed form $g(\theta)=\mathbf v_1\cos(\alpha\theta)+\mathbf v_2\sin(\alpha\theta)$ from which every subsequent computation --- the squared distance to the cone point, the chord law on a circle of constant radius, the angular speed --- is read off.
--
--   The proof is an energy argument rather than an appeal to a general existence-and-uniqueness theorem. Subtracting the candidate solution leaves a function $F$ with $F''=-\alpha^2F$, $F(0)=0$ and $F'(0)=0$; the quantity $\|F'\|^2+\alpha^2\|F\|^2$ has vanishing derivative, hence stays at its initial value $0$, and since $\alpha\ne0$ both terms are forced to vanish. No completeness of $E$ and no finite-dimensionality are needed.
--
--   Mathlib has the Picard--Lindelöf theorem and uniqueness of ODE solutions but no solution formula for the harmonic oscillator, in the scalar case or the vector-valued one.
-- source:
--   Standard theory of linear ordinary differential equations. The use made of it here is the reduction of the harmonic map equation in polar coordinates in the proof of Theorem 3.1 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608. Mathlib has no solution formula for the harmonic oscillator.

import Mathlib

namespace HarmonicOscillator

theorem eq_cos_smul_add_sin_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g g' g'' : ℝ → E) (alpha : ℝ) (halpha : alpha ≠ 0)
    (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (heq : ∀ t, g'' t = -(alpha ^ 2) • g t) :
    ∀ t, g t = Real.cos (alpha * t) • g 0 + (Real.sin (alpha * t) / alpha) • g' 0 := by sorry

end HarmonicOscillator
