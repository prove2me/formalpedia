-- Prove2me | Theorems.Thm_LNChannels_SmallRate_theorem_3_i_size
-- name    : LNChannels.SmallRate.theorem_3_i_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:37.617275+00:00
-- url     : https://prove2.me/theorems/1a096ac4-ded1-4dde-985f-90378f6207d6
-- title:
--   Theorem 3(i): optimal size expansion
-- statement:
--   Fix $B,\lambda>0$. For every positive $r$, the size $l_2^*$ displayed after equation (2) is positive and attains the minimal unidirectional cost. As $r\downarrow0$,
--
--   $$l_2^*=\left(\frac{B\lambda}{r}\right)^{1/2}+O(r^{1/2}).$$
--
--   This gives the capital scale associated with Theorem 3(i)'s cost. **Formalization Note** The explicit size is used to express the paper's attainment claim; the Big-O constant is uniform in $r$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), pp. 6–7 (PDF 7–8), Theorem 3(i), size clause following equation (7), and the size following equation (2)

import Definitions.Def_LNChannels_SmallRate_minUniCost
import Definitions.Def_LNChannels_SmallRate_uniOptimalSize

set_option autoImplicit false
open Filter Asymptotics

namespace LNChannels.SmallRate

/-- Theorem 3(i), the channel-size clause following equation (7). -/
theorem theorem_3_i_size (lam B : ℝ) (hlam : 0 < lam) (hB : 0 < B) :
    (∀ r : ℝ, 0 < r → 0 < uniOptimalSize lam r B ∧
      LNChannels.Exact.uniCost lam r B (uniOptimalSize lam r B) = minUniCost lam r B) ∧
    (fun r : ℝ => uniOptimalSize lam r B - (B * lam / r) ^ (1 / 2 : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun r : ℝ => r ^ (1 / 2 : ℝ)) := by sorry

end LNChannels.SmallRate
