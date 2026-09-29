-- Prove2me | Theorems.Thm_Landreman3DEquilibria_volume_of_domainOmega
-- name    : Landreman3DEquilibria.volume_of_domainOmega
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T19:23:52.7012+00:00
-- url     : https://prove2.me/theorems/21286782-571a-4102-bac2-b1bd62a06bd8
-- title:
--   $V(\psi)=2\pi^2ab\,\psi$
-- statement:
--   Let $0<\epsilon<1$ and $0<\delta<(1-\epsilon)^2/4$. The Lebesgue volume of the solid torus enclosed by the flux surface $\psi=\delta$ is
--
--   $$V(\delta)=2\pi^2ab\,\delta,\qquad a=\sqrt{1+\epsilon},\quad b=\sqrt{1-\epsilon}.$$
--
--   The volume is therefore exactly proportional to the flux label, which is what makes the volume average of $\psi$ over the plasma equal to $\delta/2$ and gives the closed-form expressions for the averaged pressure, averaged field strength and volume-averaged beta of the configuration.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (2.20) with the domain (2.18)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem volume_of_domainOmega (e d : ℝ) (he : 0 < e) (he1 : e < 1) (hd : 0 < d)
    (hd' : d < (1 - e) ^ 2 / 4) :
    MeasureTheory.volume (domainOmega e d) =
      ENNReal.ofReal (2 * Real.pi ^ 2 * aCoef e * bCoef e * d) := by sorry

end Landreman3DEquilibria
