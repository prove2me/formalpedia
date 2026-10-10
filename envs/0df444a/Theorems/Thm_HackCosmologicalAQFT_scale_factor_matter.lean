-- Prove2me | Theorems.Thm_HackCosmologicalAQFT_scale_factor_matter
-- name    : HackCosmologicalAQFT.scale_factor_matter
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:57.384845+00:00
-- url     : https://prove2.me/theorems/65c3cbd0-86bd-4a7a-a33a-e48689bc873b
-- title:
--   Eq. (3.8): matter domination gives $a(t)\propto(t-t_0)^{2/3}$
-- statement:
--   Let $G>0$ and let $I\subseteq\mathbb R$ be an open, connected set of cosmological times. Let $a$ be twice continuously differentiable on $I$ with $a>0$ and $\dot a>0$ there (an expanding universe), and suppose the first Friedmann equation $H^2=\frac{8\pi G}{3}\rho$ holds on $I$ for a matter-dominated energy density
--   $$\rho(t)=\dfrac{K}{a(t)^3}\qquad(t\in I)$$
--   with a constant $K>0$. Then there are constants $C>0$ and $t_0\in\mathbb R$ such that for every $t\in I$, $t>t_0$ and
--   $$a(t)=C\,(t-t_0)^{2/3}.$$
--
--   This is the matter-dominated solution in eq. (3.8) of Hack (2016). The constant $t_0$ is the time at which the scale factor of this solution would vanish.
--
--   **Formalization Note** "$\propto$" is encoded as equality with a strictly positive constant factor. The power is the real power of the positive number $t-t_0$.
-- source:
--   T.-P. Hack, *Cosmological Applications of Algebraic Quantum Field Theory in Curved Spacetimes*, SpringerBriefs in Mathematical Physics 6, Springer, 2016, DOI 10.1007/978-3-319-21894-6 (https://doi.org/10.1007/978-3-319-21894-6), Sect. 3.1, p. 80, eq. (3.8) (with eq. (3.7))

import Mathlib
import Definitions.Def_hack_flrw_friedmann

namespace HackCosmologicalAQFT

/-- Hack 2016, Sect. 3.1, eq. (3.8): matter domination gives `a(t) ∝ (t - t₀)^{2/3}`. -/
theorem scale_factor_matter (G : ℝ) (hG : 0 < G) (a ρ : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hIc : IsPreconnected I)
    (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t) (hexp : ∀ t ∈ I, 0 < deriv a t)
    (hF1 : FirstFriedmannEq G a ρ I)
    (K : ℝ) (hK : 0 < K) (hρ : ∀ t ∈ I, ρ t = K / a t ^ 3) :
    ∃ C > 0, ∃ t₀ : ℝ, ∀ t ∈ I, t₀ < t ∧ a t = C * (t - t₀) ^ (2 / 3 : ℝ) := by sorry

end HackCosmologicalAQFT
