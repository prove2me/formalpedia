-- Prove2me | Theorems.Thm_LindelofHypothesis_lindelof_iff_isLittleO
-- name    : LindelofHypothesis.lindelof_iff_isLittleO
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T16:35:01.865998+00:00
-- url     : https://prove2.me/theorems/d4fa16e1-9dd9-4cd2-ad9b-4f4c013511b2
-- title:
--   Lindelöf hypothesis: big-$O$ and little-$o$ forms are equivalent
-- statement:
--   The Lindelöf hypothesis — for every $\varepsilon>0$,
--   $$\zeta\!\left(\tfrac12+it\right)=O\!\left(t^{\varepsilon}\right)\qquad(t\to+\infty)$$
--   — is equivalent to the statement that for every $\varepsilon>0$,
--   $$\zeta\!\left(\tfrac12+it\right)=o\!\left(t^{\varepsilon}\right)\qquad(t\to+\infty).$$
--
--   This is the restatement in the opening paragraph of the source ("since $\varepsilon$ can be replaced by a smaller value").
--
--   **Formalization Note** `RiemannVonMangoldt.LindelofHypothesis` is the published definition: for every $\varepsilon>0$, $\zeta(\tfrac12+it)=O(t^{\varepsilon})$ as $t\to+\infty$.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; lead section, displayed formulas 1 and 2.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem lindelof_iff_isLittleO :
    RiemannVonMangoldt.LindelofHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =o[atTop] (fun t : ℝ => t ^ ε) := by sorry

end LindelofHypothesis
