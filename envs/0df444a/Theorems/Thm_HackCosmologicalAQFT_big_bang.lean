-- Prove2me | Theorems.Thm_HackCosmologicalAQFT_big_bang
-- name    : HackCosmologicalAQFT.big_bang
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:43.715976+00:00
-- url     : https://prove2.me/theorems/bb0ead7b-065a-4bca-b721-4aba2d066587
-- title:
--   Sect. 3.1, p. 81: an expanding universe with $\rho+3p>0$ had a Big Bang
-- statement:
--   Let $G>0$ and let $a,\rho,p:\mathbb R\to\mathbb R$ be the scale factor, energy density and pressure. Assume:
--
--   1. $a$ is continuous on $\mathbb R$;
--   2. on the open set $\{t: a(t)>0\}$, $a$ is twice continuously differentiable and satisfies the second Friedmann equation
--   $$\frac{\ddot a}{a}=-\frac{4\pi G}{3}(\rho+3p);$$
--   3. $\rho(t)+3p(t)>0$ whenever $a(t)>0$;
--   4. at some time $t_1$ the universe exists and expands: $a(t_1)>0$ and $\dot a(t_1)>0$.
--
--   Then there is a finite earlier time $t_0<t_1$ at which the scale factor vanishes, a **Big Bang**, and the universe exists throughout $(t_0,t_1]$:
--   $$\exists\,t_0<t_1:\qquad a(t_0)=0\quad\text{and}\quad a(t)>0\ \text{ for all } t\in(t_0,t_1].$$
--
--   This is the statement in Hack (2016), p. 81, that the universe "must have inevitably faced a Big Bang at some point of time in the past, i.e. there has been a $t_0>-\infty$ with $a(t_0)=0$". The source notes that this already follows from the second Friedmann equation together with $\dot a>0$ and $\rho+3p>0$.
--
--   **Formalization Note** The scale factor is a total function on $\mathbb R$. Only continuity is required at the Big Bang, because physical solutions such as $a(t)=t^{1/2}$ are not differentiable at $t_0$. The source derives $\rho+3p>0$ from $\rho>0$ in the radiation era; the formal statement takes $\rho+3p>0$ (on $\{a>0\}$) directly as its hypothesis.
-- source:
--   T.-P. Hack, *Cosmological Applications of Algebraic Quantum Field Theory in Curved Spacetimes*, SpringerBriefs in Mathematical Physics 6, Springer, 2016, DOI 10.1007/978-3-319-21894-6 (https://doi.org/10.1007/978-3-319-21894-6), Sect. 3.1, p. 81 (first paragraph: 'there has been a $t_0>-\infty$ with $a(t_0)=0$ … follows already from the second Friedmann equation and the assumptions $\dot a>0$, $\rho>0$, since then $\rho+3p>0$ and therefore $\ddot a<0$')

import Mathlib
import Definitions.Def_hack_flrw_friedmann

namespace HackCosmologicalAQFT

/-- Hack 2016, Sect. 3.1, p. 81: occurrence of a Big Bang. -/
theorem big_bang (G : ℝ) (hG : 0 < G) (a ρ p : ℝ → ℝ)
    (ha_cont : Continuous a)
    (ha_diff : ContDiffOn ℝ 2 a {t | 0 < a t})
    (hF2 : SecondFriedmannEq G a ρ p {t | 0 < a t})
    (hSEC : ∀ t, 0 < a t → 0 < ρ t + 3 * p t)
    (t₁ : ℝ) (ha₁ : 0 < a t₁) (hexp : 0 < deriv a t₁) :
    ∃ t₀ < t₁, a t₀ = 0 ∧ ∀ t ∈ Set.Ioc t₀ t₁, 0 < a t := by sorry

end HackCosmologicalAQFT
