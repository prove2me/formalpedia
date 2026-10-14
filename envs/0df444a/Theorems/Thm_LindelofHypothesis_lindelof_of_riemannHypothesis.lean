-- Prove2me | Theorems.Thm_LindelofHypothesis_lindelof_of_riemannHypothesis
-- name    : LindelofHypothesis.lindelof_of_riemannHypothesis
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:45:49.637929+00:00
-- url     : https://prove2.me/theorems/c2d77b5d-db8a-4044-bf47-ab7ab73b5836
-- title:
--   The Riemann hypothesis implies the Lindelöf hypothesis
-- statement:
--   Assume the Riemann hypothesis: every zero $s$ of $\zeta$ other than the trivial zeros $-2,-4,-6,\dots$ has $\operatorname{Re}s=\tfrac12$. Then the Lindelöf hypothesis holds: for every $\varepsilon>0$,
--   $$\zeta\!\left(\tfrac12+it\right)=O\!\left(t^{\varepsilon}\right)\qquad(t\to+\infty).$$
--
--   **Formalization Note** The Riemann hypothesis is Mathlib's `RiemannHypothesis`. `RiemannVonMangoldt.LindelofHypothesis` is the published definition: for every $\varepsilon>0$, $\zeta(\tfrac12+it)=O(t^{\varepsilon})$ as $t\to+\infty$.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; lead section ("This hypothesis is implied by the Riemann hypothesis") and section "Relation to the Riemann hypothesis".

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem lindelof_of_riemannHypothesis (hRH : RiemannHypothesis) : RiemannVonMangoldt.LindelofHypothesis := by sorry

end LindelofHypothesis
