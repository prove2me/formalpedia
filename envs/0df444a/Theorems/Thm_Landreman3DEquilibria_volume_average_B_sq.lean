-- Prove2me | Theorems.Thm_Landreman3DEquilibria_volume_average_B_sq
-- name    : Landreman3DEquilibria.volume_average_B_sq
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T19:35:55.158156+00:00
-- url     : https://prove2.me/theorems/f9b09b35-aedb-485e-8ea9-bd11eb0f41eb
-- title:
--   Eq. (2.27): $\langle|B|^2\rangle_V=1-\epsilon^2/2+\delta$
-- statement:
--   Let $0<\epsilon<1$ and $0<\delta<(1-\epsilon)^2/4$, and let $\Omega_\delta$ be the plasma domain with volume $V(\delta)=2\pi^2ab\delta$. The integral of the squared field strength over the plasma equals
--
--   $$\int_{\Omega_\delta}|B|^2\,d^3x=V(\delta)\Big(1-\frac{\epsilon^2}{2}+\delta\Big),$$
--
--   equivalently $\langle|B|^2\rangle_V=1-\epsilon^2/2+\delta$ for the volume average.
--
--   The square root of this quantity is the average field strength used in the stellarator literature (the quantity `volavgB` of the VMEC code), and together with $\langle p\rangle_V=p_a-\delta$ it gives the volume-averaged beta $\beta_V=2(p_b+\delta)/(1-\epsilon^2/2+\delta)$. These closed forms are the benchmarks the source proposes for numerical equilibrium codes.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (2.27) together with eq. (2.20)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem volume_average_B_sq (e d : ℝ) (he : 0 < e) (he1 : e < 1) (hd : 0 < d)
    (hd' : d < (1 - e) ^ 2 / 4) :
    ∫ x in domainOmega e d, normSq (Bfield e x) =
      2 * Real.pi ^ 2 * aCoef e * bCoef e * d * (1 - e ^ 2 / 2 + d) := by sorry

end Landreman3DEquilibria
