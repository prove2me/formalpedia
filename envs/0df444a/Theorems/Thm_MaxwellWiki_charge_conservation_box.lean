-- Prove2me | Theorems.Thm_MaxwellWiki_charge_conservation_box
-- name    : MaxwellWiki.charge_conservation_box
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T20:06:57.348701+00:00
-- url     : https://prove2.me/theorems/d05f8997-a76e-4dc6-9dfe-fa536249de53
-- title:
--   Charge conservation in a fixed volume: $\frac{d}{dt}Q_\Omega=-\oint_{\partial\Omega}\mathbf J\cdot d\mathbf S$
-- statement:
--   **Charge conservation in a fixed volume.** Let $\varepsilon_0>0$, $\mu_0>0$, and let $\mathbf E,\mathbf B,\mathbf J,\rho$ satisfy Maxwell's microscopic equations in SI units at every time and point, with $\mathbf E$ and $\mathbf B$ of class $C^2$ jointly in $(t,x)$. Let $a\le b$ in $\mathbb{R}^3$ and let $\Omega=[a_0,b_0]\times[a_1,b_1]\times[a_2,b_2]$ be a fixed box. Then the enclosed charge $Q_\Omega(t)=\iiint_\Omega\rho(t,x)\,dV$ is differentiable at every time $t$, and
--   $$\frac{d}{dt}Q_\Omega(t)=\frac{d}{dt}\iiint_\Omega\rho\,dV=-\oint_{\partial\Omega}\mathbf J(t,\cdot)\cdot d\mathbf S=-I_{\partial\Omega}(t).$$
--
--   This is the integral form of charge conservation: the rate of change of the charge in a fixed volume equals minus the net current flowing out through its boundary. In particular, if no current crosses $\partial\Omega$, the enclosed charge is constant.
--
--   **Formalization Note** The article's fixed volume $\Omega$ is arbitrary; this statement takes $\Omega$ to be a rectangular box, for which the outward flux is the explicit sum of face integrals from the shared definition file.
-- source:
--   Wikipedia, "Maxwell's equations", https://en.wikipedia.org/wiki/Maxwell%27s_equations (24-page PDF snapshot supplied by the proposer), section "Charge conservation" (p. 9 of the snapshot): "By the Gauss divergence theorem, this means the rate of change of charge in a fixed volume equals the net current flowing through the boundary: $\frac{d}{dt}Q_\Omega=\frac{d}{dt}\iiint_\Omega\rho\,dV=-\oint_{\partial\Omega}\mathbf J\cdot d\mathbf S=-I_{\partial\Omega}$."

import Mathlib
import Definitions.Def_MaxwellWiki_Defs

open MaxwellWiki

namespace MaxwellWiki

theorem charge_conservation_box (ε₀ μ₀ : ℝ) (hε₀ : 0 < ε₀) (hμ₀ : 0 < μ₀)
    (E B J : ℝ → Vec3 → Vec3) (ρ : ℝ → Vec3 → ℝ)
    (hE : ContDiff ℝ 2 (Function.uncurry E)) (hB : ContDiff ℝ 2 (Function.uncurry B))
    (hM : IsMaxwellSolution ε₀ μ₀ E B J ρ) (a b : Vec3) (hab : a ≤ b) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in Set.Icc a b, ρ s x) (-boxFlux (J t) a b) t := by sorry

end MaxwellWiki
