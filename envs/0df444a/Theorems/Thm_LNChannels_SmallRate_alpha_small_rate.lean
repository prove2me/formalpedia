-- Prove2me | Theorems.Thm_LNChannels_SmallRate_alpha_small_rate
-- name    : LNChannels.SmallRate.alpha_small_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:55.412677+00:00
-- url     : https://prove2.me/theorems/262f3484-2817-46a3-acf4-2ec398d819c2
-- title:
--   Small-rate expansion of the characteristic roots
-- statement:
--   Fix $\lambda>0$. At equal payment rates, equation (4) gives $\alpha_\pm=1+(r\pm\sqrt{r^2+4r\lambda})/(2\lambda)$ for $r>0$. As $r\downarrow0$,
--
--   $$\alpha_\pm=1\pm\sqrt{r/\lambda}+\frac{r}{2\lambda}+O(r^{3/2}).$$
--
--   This records the root expansion used in the proof of Theorem 3(ii). **Formalization Note** Each Big-O constant may depend on fixed $\lambda$, but is uniform in $r$ near zero.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 12 (PDF 13), proof of Theorem 3(ii), α± display

import Definitions.Def_LNChannels_Exact_alphaPlus
import Definitions.Def_LNChannels_Exact_alphaMinus

set_option autoImplicit false
open Filter Asymptotics

namespace LNChannels.SmallRate

/-- Expansion of the two roots in the proof of Theorem 3(ii), p. 12. -/
theorem alpha_small_rate (lam : ℝ) (hlam : 0 < lam) :
    (∀ r : ℝ, 0 < r →
      LNChannels.Exact.alphaPlus lam lam r = 1 + (r + Real.sqrt (r ^ 2 + 4 * r * lam)) / (2 * lam) ∧
      LNChannels.Exact.alphaMinus lam lam r = 1 + (r - Real.sqrt (r ^ 2 + 4 * r * lam)) / (2 * lam)) ∧
    (fun r : ℝ => LNChannels.Exact.alphaPlus lam lam r -
      (1 + Real.sqrt (r / lam) + r / (2 * lam)))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun r : ℝ => r ^ (3 / 2 : ℝ)) ∧
    (fun r : ℝ => LNChannels.Exact.alphaMinus lam lam r -
      (1 - Real.sqrt (r / lam) + r / (2 * lam)))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun r : ℝ => r ^ (3 / 2 : ℝ)) := by sorry

end LNChannels.SmallRate
