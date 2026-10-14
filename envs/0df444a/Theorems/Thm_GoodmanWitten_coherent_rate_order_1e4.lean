-- Prove2me | Theorems.Thm_GoodmanWitten_coherent_rate_order_1e4
-- name    : GoodmanWitten.coherent_rate_order_1e4
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:53:40.868415+00:00
-- url     : https://prove2.me/theorems/053b2d6d-bfb9-4b13-b144-e3742a0210d8
-- title:
--   Coherent weak rates of order $10^4$ events/kg day for $m\sim M$
-- statement:
--   Let the target have mass number $A>0$ and nuclear mass $M = A\,m_N$, and consider a halo particle with coherent weak interactions of mass $m = M$, with $\bar Y = 1$ and $\bar N = 100$, halo density $\rho = 10^{-24}$ g/cm$^3$ and velocity $v = 200$ km/s. Then the counting rate $R = KF\sigma$ with the coherent cross section satisfies
--   $$
--   10^4 \le R < 10^5 \quad\text{events/kg/day},
--   $$
--   i.e. the rate is of order $10^4$ events per kilogram per day.
--
--   **Formalization Note** "Of order $10^4$" is read as $10^4 \le R < 10^5$; "$m\sim M$, $\bar Y\sim1$, $\bar N\sim100$" is read as the exact values $m=M$, $\bar Y=1$, $\bar N=100$.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3060, left column, paragraph after Eq. (2)

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem coherent_rate_order_1e4 (A : ℝ) (hA : 0 < A) :
    1e4 ≤ eventRatePerKgDay A (coherentCrossSection (nucleusMass A) (nucleusMass A) 1 100)
        1e-24 2e7 (nucleusMass A) ∧
      eventRatePerKgDay A (coherentCrossSection (nucleusMass A) (nucleusMass A) 1 100)
        1e-24 2e7 (nucleusMass A) < 1e5 := by sorry

end GoodmanWitten
