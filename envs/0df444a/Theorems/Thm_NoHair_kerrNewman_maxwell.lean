-- Prove2me | Theorems.Thm_NoHair_kerrNewman_maxwell
-- name    : NoHair.kerrNewman_maxwell
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-11T05:53:49.115552+00:00
-- url     : https://prove2.me/theorems/c5c86a9f-be51-4ff0-b03c-7af1195b1b3b
-- title:
--   The Kerr–Newman field solves the source-free curved Maxwell equation $\partial_\mu(\sqrt{|\det g|}F^{\mu\nu})=0$
-- statement:
--   Let $m,a,e\in\mathbb R$ and let $y\in\mathbb R^4$ with $r(y)>0$. For the Kerr–Newman metric $g=\eta+f\,k\otimes k$ and field $F=dA$ in Kerr–Schild coordinates, the source-free Maxwell equations hold at $y$:
--   $$\sum_{\mu}\partial_\mu\big(\sqrt{|\det g|}\,F^{\mu\nu}\big)=0\qquad\text{for every }\nu,$$
--   where $F^{\mu\nu}=g^{\mu\alpha}g^{\nu\beta}F_{\alpha\beta}$ and $g^{\mu\nu}$ is the inverse matrix of $g_{\mu\nu}$. This is the second conjunct of the Einstein–Maxwell system for the Kerr–Newman solution.
--
--   **Formalization Note** Coordinates are $y=(t,x,y,z)\in\mathbb R^4$ (`E4`), $\partial_\mu$ is `coordPartial` (the Fréchet derivative applied to the $\mu$-th basis vector), $r=$ `ksRadius a y` is the positive root of $r^4-(\rho^2-a^2)r^2-a^2z^2=0$, $k=$ `ksNull a y` $=\big(1,\frac{rx+ay}{r^2+a^2},\frac{ry-ax}{r^2+a^2},\frac zr\big)$, $A=\frac{er^3}{r^4+a^2z^2}k$ (`kerrNewmanPotential`), $F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu$ (`kerrNewmanField`), $g=\eta+fk\otimes k$ with $f=\frac{r^2(2mr-e^2)}{r^4+a^2z^2}$ (`kerrNewmanMetric`), $\eta=\mathrm{diag}(-1,1,1,1)$ (`minkowski`). The only hypothesis is $r(y)>0$; no sign condition on $m,a,e$.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195 (the Kerr–Newman family as the model solutions of the Einstein–Maxwell equations), together with the Kerr–Schild form of the Kerr–Newman metric and potential, Wikipedia "Kerr–Newman metric", section "Kerr–Schild coordinates" (E. T. Newman et al., J. Math. Phys. 6 (1965) 918; Debever, Kamran, McLenaghan, J. Math. Phys. 25 (1984) 1955); listed as part of milestone NoHair.kerrNewman_einsteinMaxwell of the mission

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Kerr–Newman satisfies the source-free Maxwell equation.** Wherever `r > 0`,
`∂_μ (√|det g| F^{μν}) = 0` for the Kerr–Newman metric `g` and field `F`. -/
theorem kerrNewman_maxwell (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ ν, ∑ μ, coordPartial
      (fun z => Real.sqrt |(kerrNewmanMetric m a e z).det|
        * raiseBoth (kerrNewmanMetric m a e) (kerrNewmanField a e) z μ ν) μ y = 0 := by
  sorry

end NoHair
