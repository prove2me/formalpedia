-- Prove2me | Theorems.Thm_NoHair_kerrNewman_flat_maxwell
-- name    : NoHair.kerrNewman_flat_maxwell
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-11T05:54:39.850578+00:00
-- url     : https://prove2.me/theorems/2a76a228-69dd-4f40-a775-d8e98e4f6349
-- title:
--   The Kerr–Newman potential solves the flat-space Maxwell equations in Kerr–Schild coordinates
-- statement:
--   Let $a,e\in\mathbb R$ and let $y\in\mathbb R^4$ with $r(y)>0$. The Kerr–Newman field $F=dA$, $A_\mu=\frac{e\,r^3}{r^4+a^2z^2}k_\mu$, solves the source-free Maxwell equations of flat Minkowski space at $y$:
--   $$\sum_\mu\partial_\mu\big(\eta^{\mu\alpha}\eta^{\nu\beta}F_{\alpha\beta}\big)=0\qquad\text{for every }\nu .$$
--   Together with the algebraic facts that $k$ is $\eta$-null (so $\det g=-1$ and $g^{-1}=\eta-f\,k^\sharp\otimes k^\sharp$) and that $k$ is an eigenvector of $F$ ($F_{\alpha\beta}k^{\sharp\beta}=\lambda k_\alpha$), it implies the curved Maxwell equation $\partial_\mu(\sqrt{|\det g|}F^{\mu\nu})=0$ for the Kerr–Newman metric, because then $\sqrt{|\det g|}F^{\mu\nu}=\eta^{\mu\alpha}\eta^{\nu\beta}F_{\alpha\beta}$ wherever $r>0$. This is the classical fact that the Kerr–Newman field is a flat-space Maxwell field in Kerr–Schild coordinates (the "single copy" of the Kerr–Schild form).
--
--   **Formalization Note** Coordinates are $y=(t,x,y,z)\in\mathbb R^4$ (`E4`), $\partial_\mu$ is `coordPartial` (the Fréchet derivative applied to the $\mu$-th basis vector), $r=$ `ksRadius a y` is the positive root of $r^4-(\rho^2-a^2)r^2-a^2z^2=0$, $k=$ `ksNull a y` $=\big(1,\frac{rx+ay}{r^2+a^2},\frac{ry-ax}{r^2+a^2},\frac zr\big)$, $A=\frac{er^3}{r^4+a^2z^2}k$ (`kerrNewmanPotential`), $F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu$ (`kerrNewmanField`), $g=\eta+fk\otimes k$ with $f=\frac{r^2(2mr-e^2)}{r^4+a^2z^2}$ (`kerrNewmanMetric`), $\eta=\mathrm{diag}(-1,1,1,1)$ (`minkowski`). The only hypothesis is $r(y)>0$; no sign condition on $m,a,e$.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195 (the Kerr–Newman family as the model solutions of the Einstein–Maxwell equations), together with the Kerr–Schild form of the Kerr–Newman metric and potential, Wikipedia "Kerr–Newman metric", section "Kerr–Schild coordinates" (E. T. Newman et al., J. Math. Phys. 6 (1965) 918; Debever, Kamran, McLenaghan, J. Math. Phys. 25 (1984) 1955); listed as part of milestone NoHair.kerrNewman_einsteinMaxwell of the mission

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- Flat-space source-free Maxwell equations for the Kerr–Newman potential in Kerr–Schild
coordinates: `∂_μ (η^{μα} η^{νβ} F_{αβ}) = 0` wherever the Kerr–Schild radius is positive. -/
theorem kerrNewman_flat_maxwell (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ ν, ∑ μ, coordPartial
      (fun z => ∑ α, ∑ β, minkowski μ α * minkowski ν β * kerrNewmanField a e z α β) μ y = 0 := by
  sorry

end NoHair
