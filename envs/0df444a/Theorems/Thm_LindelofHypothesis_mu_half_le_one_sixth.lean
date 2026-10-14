-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_half_le_one_sixth
-- name    : LindelofHypothesis.mu_half_le_one_sixth
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:42:19.955218+00:00
-- url     : https://prove2.me/theorems/fa4365c3-9396-40c0-9822-97e0bb47de02
-- title:
--   Weyl–Hardy–Littlewood bound: $\mu(\tfrac12)\le\tfrac16$
-- statement:
--   The growth exponent on the critical line satisfies
--   $$\mu\!\left(\tfrac12\right)\le\tfrac16 ,$$
--   i.e. $\zeta(\tfrac12+it)=O(t^{1/6+\varepsilon})$ for every $\varepsilon>0$.
--
--   This is the bound of Hardy and Littlewood (1916, 1923), obtained from Weyl's method for exponential sums applied to the approximate functional equation; it is the first improvement on the convexity bound.
--
--   **Formalization Note** $\mu$ is `LindelofHypothesis.mu`, valued in the extended reals.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The μ function", sentence "The upper bound of 1/4 was lowered by Hardy and Littlewood to 1/6", and second row of the table (Hardy & Littlewood 1916, 1923).

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem mu_half_le_one_sixth : mu (1 / 2) ≤ ((1 / 6 : ℝ) : EReal) := by sorry

end LindelofHypothesis
