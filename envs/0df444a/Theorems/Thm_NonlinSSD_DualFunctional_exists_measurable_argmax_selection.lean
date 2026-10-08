-- Prove2me | Theorems.Thm_NonlinSSD_DualFunctional_exists_measurable_argmax_selection
-- name    : NonlinSSD.DualFunctional.exists_measurable_argmax_selection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:21:00.211248+00:00
-- url     : https://prove2.me/theorems/5190696f-e391-410f-9826-c2543c67e1cf
-- title:
--   p. 13, before Theorem 5 — a measurable selection X(ω) ∈ argmax_t [v(t) − ζ(ω)t] with X ∈ [a, b] a.s.
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $a\le b$, $v\in\mathcal U_1([a,b])$, and let $\zeta$ be a random variable with
--   $$0\le\zeta\le v'_-(a)\quad\text{a.s.}$$
--   Then there is a measurable random variable $X$ such that $X\in[a,b]$ almost surely and
--   $$X(\omega)\in\operatorname*{argmax}_{t\in\mathbb R}\,[v(t)-\zeta(\omega)t]\quad\text{for $P$-almost all }\omega .$$
--
--   Such a selection is a bounded, hence integrable, maximizer of $\mathbb E[v(X)-\zeta X]$, which is how the supremum in (34) is attained, and it is the random variable whose law is the subgradient in Theorem 5.
--
--   **Formalization Note** $\zeta$ is assumed almost-everywhere measurable (any element of $\mathcal L_\infty$ or $\mathcal L_1$ is); the selection is measurable outright. "$X(\omega)\in\operatorname{argmax}$" is written as: for almost every $\omega$, $v(t)-\zeta(\omega)t\le v(X(\omega))-\zeta(\omega)X(\omega)$ for every real $t$. The paper cites Rockafellar–Wets, Theorem 14.37, for existence.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 13, paragraph before Theorem 5

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Basic

open MeasureTheory

namespace NonlinSSD.DualFunctional

theorem exists_measurable_argmax_selection {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (a b : ℝ) (hab : a ≤ b) (v : ℝ → ℝ) (hv : v ∈ NonlinSSD.Optimality.U1 a b)
    (ζ : Ω → ℝ) (hζm : AEMeasurable ζ P)
    (hζ : ∀ᵐ ω ∂P, 0 ≤ ζ ω ∧ ζ ω ≤ leftDeriv v a) :
    ∃ X : Ω → ℝ, Measurable X ∧ (∀ᵐ ω ∂P, X ω ∈ Set.Icc a b) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ, v t - ζ ω * t ≤ v (X ω) - ζ ω * X ω := by sorry

end NonlinSSD.DualFunctional
