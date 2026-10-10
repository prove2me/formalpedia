-- Prove2me | Theorems.Thm_MassEnergyEquivalence_relEnergy_hasSum
-- name    : MassEnergyEquivalence.relEnergy_hasSum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:14:09.35926+00:00
-- url     : https://prove2.me/theorems/72bc8e9d-49cb-40cd-8a80-4ca77f725f92
-- title:
--   Power series $E = m_0c^2\big[1 + \tfrac12(v/c)^2 + \tfrac38(v/c)^4 + \tfrac5{16}(v/c)^6 + \cdots\big]$
-- statement:
--   Let $c>0$, $m_0\ge0$ and $\mathbf v\in\mathbb R^3$ with speed $v=|\mathbf v|<c$. The relativistic energy $E=\gamma m_0c^2$ is the sum of the convergent power series
--
--   $$
--   E = m_0c^2\sum_{n=0}^{\infty}\frac{1}{4^n}\binom{2n}{n}\Big(\frac{v}{c}\Big)^{2n}
--     = m_0c^2\left[1+\frac12\Big(\frac vc\Big)^2+\frac38\Big(\frac vc\Big)^4+\frac5{16}\Big(\frac vc\Big)^6+\cdots\right].
--   $$
--
--   This is the expansion used in the article to compare the relativistic energy with its Newtonian approximation.
--
--   **Formalization Note** The article writes only the first four coefficients followed by "$\cdots$"; the general coefficient $\binom{2n}{n}/4^n$ (the binomial series of $(1-x)^{-1/2}$) is the standard one and agrees with $1,\tfrac12,\tfrac38,\tfrac5{16}$. Convergence is expressed as unconditional summability (`HasSum`), which for these non-negative terms is ordinary convergence.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Low-speed approximation (p. 6), first display: $E = m_0c^2[1 + \tfrac12(v/c)^2 + \tfrac38(v/c)^4 + \tfrac5{16}(v/c)^6 + \dots]$.

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem relEnergy_hasSum (c m : ℝ) (v : Vec3) (hc : 0 < c) (hm : 0 ≤ m) (hv : ‖v‖ < c) :
    HasSum (fun n : ℕ => m * c ^ 2 * ((Nat.centralBinom n : ℝ) / 4 ^ n) * (‖v‖ / c) ^ (2 * n))
      (relEnergy c m v) := by sorry

end MassEnergyEquivalence
