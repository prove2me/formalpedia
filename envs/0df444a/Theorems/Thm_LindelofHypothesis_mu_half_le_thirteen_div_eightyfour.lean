-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_half_le_thirteen_div_eightyfour
-- name    : LindelofHypothesis.mu_half_le_thirteen_div_eightyfour
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:42:46.845379+00:00
-- url     : https://prove2.me/theorems/9dcf5194-9890-4827-9244-a580502ce2fe
-- title:
--   Bourgain's bound: $\mu(\tfrac12)\le\tfrac{13}{84}$
-- statement:
--   The growth exponent on the critical line satisfies
--   $$\mu\!\left(\tfrac12\right)\le\tfrac{13}{84}\approx0.1548 ,$$
--   i.e. $\zeta(\tfrac12+it)=O(t^{13/84+\varepsilon})$ for every $\varepsilon>0$.
--
--   This is Bourgain's 2017 bound, the last entry of the table of known bounds for $\mu(\tfrac12)$ in the source.
--
--   **Formalization Note** $\mu$ is `LindelofHypothesis.mu`, valued in the extended reals.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; table of bounds for μ(1/2), last row (13/84, 0.1548, Bourgain 2017).

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem mu_half_le_thirteen_div_eightyfour : mu (1 / 2) ≤ ((13 / 84 : ℝ) : EReal) := by sorry

end LindelofHypothesis
