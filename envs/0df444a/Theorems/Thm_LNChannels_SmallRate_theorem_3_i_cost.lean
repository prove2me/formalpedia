-- Prove2me | Theorems.Thm_LNChannels_SmallRate_theorem_3_i_cost
-- name    : LNChannels.SmallRate.theorem_3_i_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:34.148906+00:00
-- url     : https://prove2.me/theorems/787b5bfe-b3da-4e3f-8938-6cbc32e305c0
-- title:
--   Theorem 3(i): square-root cost law
-- statement:
--   Fix a positive reset cost $B$ and payment rate $\lambda$. As the discount rate $r$ decreases to zero through positive values, the minimal unidirectional channel cost satisfies
--
--   $$c^{\mathrm{opt}}(0,\lambda)=2\left(\frac{B\lambda}{r}\right)^{1/2}-\frac B2+O(r^{1/2}).$$
--
--   This is the unidirectional comparison for the symmetric channel's cube-root law. **Formalization Note** The Big-O constant may depend on fixed $B$ and $\lambda$, but is uniform in $r$ near zero. Sizes range over positive reals.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 7 (PDF 8), Theorem 3(i), equation (7), cost clause

import Definitions.Def_LNChannels_SmallRate_minUniCost

set_option autoImplicit false
open Filter Asymptotics

namespace LNChannels.SmallRate

/-- Theorem 3(i), equation (7), cost clause; r tends to zero from above. -/
theorem theorem_3_i_cost (lam B : ℝ) (hlam : 0 < lam) (hB : 0 < B) :
    (fun r : ℝ => minUniCost lam r B -
      (2 * (B * lam / r) ^ (1 / 2 : ℝ) - B / 2)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun r : ℝ => r ^ (1 / 2 : ℝ)) := by sorry

end LNChannels.SmallRate
