-- Prove2me | Theorems.Thm_HackCosmologicalAQFT_continuity_eq_of_friedmann
-- name    : HackCosmologicalAQFT.continuity_eq_of_friedmann
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:52.817264+00:00
-- url     : https://prove2.me/theorems/afcf0bba-8873-4ba8-9dae-445ef44fd842
-- title:
--   Eq. (3.6): the Friedmann equations imply $\dot\rho+3H(\rho+p)=0$
-- statement:
--   Let $G>0$, let $I\subseteq\mathbb R$ be an open set of cosmological times, and let $a,\rho,p:\mathbb R\to\mathbb R$ be the scale factor, energy density and pressure. Assume $a$ is twice continuously differentiable on $I$ with $a>0$ there, and that both Friedmann equations hold on $I$:
--   $$H^2=\frac{8\pi G}{3}\rho,\qquad \frac{\ddot a}{a}=-\frac{4\pi G}{3}(\rho+3p),\qquad H=\frac{\dot a}{a}.$$
--   Then for every $t\in I$ the energy density obeys the conservation law
--   $$\dot\rho(t)+3H(t)\big(\rho(t)+p(t)\big)=0.$$
--
--   This is the observation in Hack (2016), p. 80, that eq. (3.6), the FLRW form of $\nabla^\mu T_{\mu\nu}=0$, can be obtained directly from the Friedmann equations.
--
--   **Formalization Note** No differentiability of $\rho$ is assumed. On $I$ the first Friedmann equation determines $\rho$ from $a$, so $\dot\rho$ is meaningful.
-- source:
--   T.-P. Hack, *Cosmological Applications of Algebraic Quantum Field Theory in Curved Spacetimes*, SpringerBriefs in Mathematical Physics 6, Springer, 2016, DOI 10.1007/978-3-319-21894-6 (https://doi.org/10.1007/978-3-319-21894-6), Sect. 3.1, p. 80, eqs. (3.5)–(3.6)

import Mathlib
import Definitions.Def_hack_flrw_friedmann

namespace HackCosmologicalAQFT

/-- Hack 2016, Sect. 3.1, eq. (3.6): the Friedmann equations imply `ρ̇ + 3H(ρ + p) = 0`. -/
theorem continuity_eq_of_friedmann (G : ℝ) (hG : 0 < G) (a ρ p : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t)
    (hF1 : FirstFriedmannEq G a ρ I) (hF2 : SecondFriedmannEq G a ρ p I) :
    ∀ t ∈ I, deriv ρ t + 3 * hubbleRate a t * (ρ t + p t) = 0 := by sorry

end HackCosmologicalAQFT
