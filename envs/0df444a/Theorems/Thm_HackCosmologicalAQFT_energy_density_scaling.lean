-- Prove2me | Theorems.Thm_HackCosmologicalAQFT_energy_density_scaling
-- name    : HackCosmologicalAQFT.energy_density_scaling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:28.248406+00:00
-- url     : https://prove2.me/theorems/02672749-1bed-4bb9-807a-cf2f938023be
-- title:
--   Eq. (3.7): $\rho_{\rm rad}\propto a^{-4}$, $\rho_{\rm mat}\propto a^{-3}$, $\rho_\Lambda$ constant
-- statement:
--   Let $I\subseteq\mathbb R$ be an open, connected set of cosmological times. Let $a$ be twice continuously differentiable on $I$ with $a>0$ there, and let the energy density $\rho$ be differentiable on $I$. Suppose the pressure obeys the equation of state $p=w\rho$ on $I$ with
--   $$w\in\{\tfrac13,\ 0,\ -1\}\qquad\text{(radiation, matter, cosmological constant)},$$
--   and that the conservation law $\dot\rho+3H(\rho+p)=0$, $H=\dot a/a$, holds on $I$. Then there is a constant $C\in\mathbb R$ such that
--   $$\rho(t)=C\,a(t)^{-3(1+w)}\qquad\text{for all }t\in I,$$
--   that is, $\rho\propto a^{-4}$ for radiation, $\rho\propto a^{-3}$ for matter, and $\rho$ is constant for a cosmological constant.
--
--   In Hack's normalisation, $C=\rho_0\Omega_{\rm rad}$, $\rho_0\Omega_{\rm mat}$, $\rho_0\Omega_\Lambda$ respectively.
--
--   **Formalization Note** The power $a^{-3(1+w)}$ is the real power of the positive number $a(t)$.
-- source:
--   T.-P. Hack, *Cosmological Applications of Algebraic Quantum Field Theory in Curved Spacetimes*, SpringerBriefs in Mathematical Physics 6, Springer, 2016, DOI 10.1007/978-3-319-21894-6 (https://doi.org/10.1007/978-3-319-21894-6), Sect. 3.1, pp. 79–80, eqs. (3.4), (3.6), (3.7)

import Mathlib
import Definitions.Def_hack_flrw_friedmann

namespace HackCosmologicalAQFT

/-- Hack 2016, Sect. 3.1, eqs. (3.4), (3.6), (3.7): for radiation (`w = 1/3`), matter (`w = 0`)
and a cosmological constant (`w = -1`), conservation forces `ρ ∝ a^{-3(1+w)}`. -/
theorem energy_density_scaling (a ρ p : ℝ → ℝ) (w : ℝ) (hw : w = 1 / 3 ∨ w = 0 ∨ w = -1)
    (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t)
    (hρ : DifferentiableOn ℝ ρ I) (hp : ∀ t ∈ I, p t = w * ρ t)
    (hcons : ∀ t ∈ I, deriv ρ t + 3 * hubbleRate a t * (ρ t + p t) = 0) :
    ∃ C : ℝ, ∀ t ∈ I, ρ t = C * a t ^ (-(3 * (1 + w))) := by sorry

end HackCosmologicalAQFT
