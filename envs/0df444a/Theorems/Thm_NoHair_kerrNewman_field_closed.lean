-- Prove2me | Theorems.Thm_NoHair_kerrNewman_field_closed
-- name    : NoHair.kerrNewman_field_closed
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-11T05:53:01.178978+00:00
-- url     : https://prove2.me/theorems/9c810d9f-30fa-4607-8131-cb6b04375499
-- title:
--   The Kerr–Newman electromagnetic field is closed: $\partial_{[\lambda}F_{\mu\nu]}=0$
-- statement:
--   Let $a,e\in\mathbb R$ and let $y\in\mathbb R^4$ be a point with $r(y)>0$. The Kerr–Newman field $F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu$, built from the potential $A_\mu=\frac{e\,r^3}{r^4+a^2z^2}\,k_\mu$ in Kerr–Schild coordinates, satisfies the homogeneous Maxwell equations (Bianchi identity) at $y$:
--   $$\partial_\lambda F_{\mu\nu}+\partial_\mu F_{\nu\lambda}+\partial_\nu F_{\lambda\mu}=0\qquad\text{for all }\lambda,\mu,\nu.$$
--   This is the third conjunct of the Einstein–Maxwell system for the Kerr–Newman solution. It holds because $A$ is smooth near every point with $r>0$ and second partial derivatives commute.
--
--   **Formalization Note** Coordinates are $y=(t,x,y,z)\in\mathbb R^4$ (`E4`), $\partial_\mu$ is `coordPartial` (the Fréchet derivative applied to the $\mu$-th basis vector), $r=$ `ksRadius a y` is the positive root of $r^4-(\rho^2-a^2)r^2-a^2z^2=0$, $k=$ `ksNull a y` $=\big(1,\frac{rx+ay}{r^2+a^2},\frac{ry-ax}{r^2+a^2},\frac zr\big)$, $A=\frac{er^3}{r^4+a^2z^2}k$ (`kerrNewmanPotential`), $F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu$ (`kerrNewmanField`), $g=\eta+fk\otimes k$ with $f=\frac{r^2(2mr-e^2)}{r^4+a^2z^2}$ (`kerrNewmanMetric`), $\eta=\mathrm{diag}(-1,1,1,1)$ (`minkowski`). The only hypothesis is $r(y)>0$; no sign condition on $m,a,e$.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195 (the Kerr–Newman family as the model solutions of the Einstein–Maxwell equations), together with the Kerr–Schild form of the Kerr–Newman metric and potential, Wikipedia "Kerr–Newman metric", section "Kerr–Schild coordinates" (E. T. Newman et al., J. Math. Phys. 6 (1965) 918; Debever, Kamran, McLenaghan, J. Math. Phys. 25 (1984) 1955); listed as part of milestone NoHair.kerrNewman_einsteinMaxwell of the mission

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Bianchi identity for the Kerr–Newman field.** Wherever `r > 0`, the field `F = dA`
satisfies `∂_λ F_{μν} + ∂_μ F_{νλ} + ∂_ν F_{λμ} = 0`. -/
theorem kerrNewman_field_closed (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ l μ ν, coordPartial (fun z => kerrNewmanField a e z μ ν) l y
      + coordPartial (fun z => kerrNewmanField a e z ν l) μ y
      + coordPartial (fun z => kerrNewmanField a e z l μ) ν y = 0 := by
  sorry

end NoHair
