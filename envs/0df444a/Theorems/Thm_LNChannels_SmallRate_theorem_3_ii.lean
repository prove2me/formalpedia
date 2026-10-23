-- Prove2me | Theorems.Thm_LNChannels_SmallRate_theorem_3_ii
-- name    : LNChannels.SmallRate.theorem_3_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:43.453977+00:00
-- url     : https://prove2.me/theorems/720b433d-7759-405d-8251-3440f1a39bbd
-- title:
--   Theorem 3(ii): cube-root cost law
-- statement:
--   Fix a positive reset cost $B$ and equal positive payment rates $\lambda$ in the two directions. As the discount rate $r$ decreases to zero through positive values, the infimum of the symmetric bidirectional channel cost over $l_1,l_2>0$ satisfies
--
--   $$c^{\mathrm{opt}}(\lambda,\lambda)=3\left(\frac{2B\lambda}{r}\right)^{1/3}-\frac B6+O(r^{1/3}).$$
--
--   This is the cost advantage's asymptotic scale at small discount rates. **Formalization Note** The theorem captures the cost clause of Theorem 3(ii). Its separate claim that optimal sizes obey $l_1=l_2=(2B\lambda/r)^{1/3}+O(r^{1/3})$ is outside this proposal. The Big-O constant may depend on fixed $B,\lambda$, not on $r$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 7 (PDF 8), Theorem 3(ii), equation (8), cost clause

import Definitions.Def_LNChannels_SmallRate_minSymCost

set_option autoImplicit false
open Filter Asymptotics

namespace LNChannels.SmallRate

/-- Theorem 3(ii), equation (8), cost clause; r tends to zero from above. -/
theorem theorem_3_ii (lam B : ℝ) (hlam : 0 < lam) (hB : 0 < B) :
    (fun r : ℝ => minSymCost lam r B -
      (3 * (2 * B * lam / r) ^ (1 / 3 : ℝ) - B / 6)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun r : ℝ => r ^ (1 / 3 : ℝ)) := by sorry

end LNChannels.SmallRate
