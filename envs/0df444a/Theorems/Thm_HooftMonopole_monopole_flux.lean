-- Prove2me | Theorems.Thm_HooftMonopole_monopole_flux
-- name    : HooftMonopole.monopole_flux
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T20:14:15.819783+00:00
-- url     : https://prove2.me/theorems/b446c13f-0cc9-4b9b-9258-76e55ee15151
-- title:
--   Eq. (2.21): the total magnetic flux has magnitude $4\pi/e$
-- statement:
--   Let $e > 0$, $F > 0$, and let $B_k = \frac12\varepsilon_{kij}F_{ij}$ be the magnetic field of the electromagnetic tensor (2.17) of the asymptotic configuration $Q_a = Fx_a/r$, $W^a_i = -\varepsilon_{iab}x_b/(er^2)$. For every radius $R > 0$, the magnetic flux through the sphere of radius $R$ about the origin has magnitude $4\pi/e$:
--   $$\Big|\,R^2\int_{S^2}B(R\omega)\cdot\omega\;d\sigma(\omega)\Big| = \frac{4\pi}{e},$$
--   where $\sigma$ is the surface measure on the unit sphere $S^2$ (total mass $4\pi$).
--
--   Magnetic flux $4\pi/e$ is Schwinger's value $eg = 1$ (2.22), twice Dirac's quantum.
--
--   **Formalization Note** The surface measure is Mathlib's `Measure.toSphere` of Lebesgue measure. The absolute value is taken because the printed sign of (2.21) and the sign that follows from (2.20) with $B_k = \frac12\varepsilon_{kij}F_{ij}$ differ; the sign is fixed by milestone (2.20).
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, p. 281, eqs. (2.20)-(2.22)

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem monopole_flux (e F : ℝ) (he : 0 < e) (hF : 0 < F) (R : ℝ) (hR : 0 < R) :
    |R ^ 2 * ∫ ω : Metric.sphere (0 : Space) 1,
        ∑ k, magneticField e (hedgehogHiggs (fun r => F / r))
            (hedgehogGauge (fun r => -1 / (e * r ^ 2))) (R • (ω : Space)) k * (ω : Space) k
        ∂(volume : Measure Space).toSphere| = 4 * π / e := by sorry

end HooftMonopole
