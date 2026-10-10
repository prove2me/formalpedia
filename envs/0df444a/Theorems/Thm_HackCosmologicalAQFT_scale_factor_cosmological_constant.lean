-- Prove2me | Theorems.Thm_HackCosmologicalAQFT_scale_factor_cosmological_constant
-- name    : HackCosmologicalAQFT.scale_factor_cosmological_constant
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:45.560908+00:00
-- url     : https://prove2.me/theorems/6d356da6-6461-40d8-a549-ca3fd57f5e0f
-- title:
--   Eq. (3.8): a cosmological constant gives $a(t)\propto e^{\sqrt{\Lambda/3}\,t}$
-- statement:
--   Let $G>0$ and let $I\subseteq\mathbb R$ be an open, connected set of cosmological times. Let $a$ be twice continuously differentiable on $I$ with $a>0$ and $\dot a>0$ there, and suppose the first Friedmann equation $H^2=\frac{8\pi G}{3}\rho$ holds on $I$ with the energy density of a cosmological constant $\Lambda>0$,
--   $$\rho(t)=\rho_\Lambda=\frac{\Lambda}{8\pi G}\qquad(t\in I).$$
--   Then there is a constant $C>0$ such that
--   $$a(t)=C\,e^{\sqrt{\Lambda/3}\,t}\qquad\text{for all }t\in I.$$
--
--   This is the $\Lambda$-dominated (de Sitter) solution in eq. (3.8) of Hack (2016).
--
--   **Formalization Note** The source leaves the relation between $\rho_\Lambda$ and $\Lambda$ implicit. The standard convention $\rho_\Lambda=\Lambda/(8\pi G)$ is the one under which eq. (3.8) has exponent $\sqrt{\Lambda/3}$.
-- source:
--   T.-P. Hack, *Cosmological Applications of Algebraic Quantum Field Theory in Curved Spacetimes*, SpringerBriefs in Mathematical Physics 6, Springer, 2016, DOI 10.1007/978-3-319-21894-6 (https://doi.org/10.1007/978-3-319-21894-6), Sect. 3.1, p. 80, eq. (3.8) (with eq. (3.7))

import Mathlib
import Definitions.Def_hack_flrw_friedmann

namespace HackCosmologicalAQFT

/-- Hack 2016, Sect. 3.1, eq. (3.8): domination by a cosmological constant `Λ > 0`
(energy density `ρ_Λ = Λ / (8πG)`) gives `a(t) ∝ exp(√(Λ/3) t)`. -/
theorem scale_factor_cosmological_constant (G : ℝ) (hG : 0 < G) (a ρ : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hIc : IsPreconnected I)
    (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t) (hexp : ∀ t ∈ I, 0 < deriv a t)
    (hF1 : FirstFriedmannEq G a ρ I)
    (Λ : ℝ) (hΛ : 0 < Λ) (hρ : ∀ t ∈ I, ρ t = Λ / (8 * Real.pi * G)) :
    ∃ C > 0, ∀ t ∈ I, a t = C * Real.exp (Real.sqrt (Λ / 3) * t) := by sorry

end HackCosmologicalAQFT
