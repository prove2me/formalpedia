-- Prove2me | Theorems.Thm_NoHair_kerrNewman_einstein
-- name    : NoHair.kerrNewman_einstein
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-11T05:54:19.815691+00:00
-- url     : https://prove2.me/theorems/29511860-2b59-4995-a0aa-33f3e4ef6f27
-- title:
--   The Kerr–Newman metric satisfies the Einstein equation with electromagnetic stress–energy source
-- statement:
--   Let $m,a,e\in\mathbb R$ and let $y\in\mathbb R^4$ with $r(y)>0$. For the Kerr–Newman metric $g=\eta+f\,k\otimes k$ and field $F=dA$ in Kerr–Schild coordinates, the Einstein equation holds at $y$:
--   $$G_{\mu\nu}=2\Big(F_{\mu\alpha}F_{\nu\beta}\,g^{\alpha\beta}-\tfrac14\,g_{\mu\nu}F_{\alpha\beta}F^{\alpha\beta}\Big)\qquad\text{for all }\mu,\nu,$$
--   where $G_{\mu\nu}=R_{\mu\nu}-\frac12Rg_{\mu\nu}$ is computed from the Christoffel symbols of $g$ (geometrized Gaussian units, right side multiplied by $8\pi$). This is the first conjunct of the Einstein–Maxwell system for the Kerr–Newman solution.
--
--   **Formalization Note** Coordinates are $y=(t,x,y,z)\in\mathbb R^4$ (`E4`), $\partial_\mu$ is `coordPartial` (the Fréchet derivative applied to the $\mu$-th basis vector), $r=$ `ksRadius a y` is the positive root of $r^4-(\rho^2-a^2)r^2-a^2z^2=0$, $k=$ `ksNull a y` $=\big(1,\frac{rx+ay}{r^2+a^2},\frac{ry-ax}{r^2+a^2},\frac zr\big)$, $A=\frac{er^3}{r^4+a^2z^2}k$ (`kerrNewmanPotential`), $F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu$ (`kerrNewmanField`), $g=\eta+fk\otimes k$ with $f=\frac{r^2(2mr-e^2)}{r^4+a^2z^2}$ (`kerrNewmanMetric`), $\eta=\mathrm{diag}(-1,1,1,1)$ (`minkowski`). The only hypothesis is $r(y)>0$; no sign condition on $m,a,e$.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195 (the Kerr–Newman family as the model solutions of the Einstein–Maxwell equations), together with the Kerr–Schild form of the Kerr–Newman metric and potential, Wikipedia "Kerr–Newman metric", section "Kerr–Schild coordinates" (E. T. Newman et al., J. Math. Phys. 6 (1965) 918; Debever, Kamran, McLenaghan, J. Math. Phys. 25 (1984) 1955); listed as part of milestone NoHair.kerrNewman_einsteinMaxwell of the mission

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Kerr–Newman satisfies the Einstein equation.** Wherever `r > 0`, the Einstein tensor of the
Kerr–Newman metric equals the (8π-scaled) Maxwell stress tensor of the Kerr–Newman field. -/
theorem kerrNewman_einstein (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ μ ν, einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν := by
  sorry

end NoHair
