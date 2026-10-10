-- Prove2me | Theorems.Thm_HackCosmologicalAQFT_strictMonoOn_of_first_friedmann
-- name    : HackCosmologicalAQFT.strictMonoOn_of_first_friedmann
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:56.377554+00:00
-- url     : https://prove2.me/theorems/76eba280-bd60-4412-8993-62d9ec9c236f
-- title:
--   Sect. 3.1, p. 80: $\rho>0$ and $\dot a>0$ once imply $a$ strictly increasing
-- statement:
--   Let $G>0$ and let $I\subseteq\mathbb R$ be an open, connected set of cosmological times. Let $a$ be twice continuously differentiable on $I$ with $a>0$ there, and suppose the first Friedmann equation $H^2=\frac{8\pi G}{3}\rho$ holds on $I$ with
--   $$\rho(t)>0\quad\text{for all }t\in I.$$
--   If $\dot a(t_1)>0$ at a single instant $t_1\in I$, then $a$ is strictly increasing on all of $I$.
--
--   This is the remark in Hack (2016), p. 80: "if $\rho>0$ for all times and $\dot a>0$ at one instant of time, then $a$ will be strictly increasing for all times." It underlies the use of $a$ and the redshift $z$ as time variables.
-- source:
--   T.-P. Hack, *Cosmological Applications of Algebraic Quantum Field Theory in Curved Spacetimes*, SpringerBriefs in Mathematical Physics 6, Springer, 2016, DOI 10.1007/978-3-319-21894-6 (https://doi.org/10.1007/978-3-319-21894-6), Sect. 3.1, p. 80 (paragraph after eq. (3.7))

import Mathlib
import Definitions.Def_hack_flrw_friedmann

namespace HackCosmologicalAQFT

/-- Hack 2016, Sect. 3.1, p. 80: if `ρ > 0` at all times and `ȧ > 0` at one instant, the first
Friedmann equation forces `a` to be strictly increasing at all times. -/
theorem strictMonoOn_of_first_friedmann (G : ℝ) (hG : 0 < G) (a ρ : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hIc : IsPreconnected I)
    (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t)
    (hF1 : FirstFriedmannEq G a ρ I) (hρ : ∀ t ∈ I, 0 < ρ t)
    (t₁ : ℝ) (ht₁ : t₁ ∈ I) (hexp : 0 < deriv a t₁) :
    StrictMonoOn a I := by sorry

end HackCosmologicalAQFT
