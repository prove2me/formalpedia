-- Prove2me | Theorems.Thm_LindelofHypothesis_lindelof_iff_moments
-- name    : LindelofHypothesis.lindelof_iff_moments
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:47:48.691968+00:00
-- url     : https://prove2.me/theorems/bef3b800-c651-4c61-92f8-2e66ac178261
-- title:
--   Lindelöf $\iff$ $\frac1T\int_0^T|\zeta(\tfrac12+it)|^{2k}dt=O(T^{\varepsilon})$ for all $k$
-- statement:
--   The Lindelöf hypothesis holds if and only if, for every positive integer $k$ and every real $\varepsilon>0$,
--   $$\frac1T\int_0^T\left|\zeta\!\left(\tfrac12+it\right)\right|^{2k}dt=O\!\left(T^{\varepsilon}\right)\qquad(T\to\infty).$$
--
--   This is the equivalence between the Lindelöf hypothesis and bounds for all even moments of $\zeta$ on the critical line.
--
--   **Formalization Note** `RiemannVonMangoldt.LindelofHypothesis` is the published definition: for every $\varepsilon>0$, $\zeta(\tfrac12+it)=O(t^{\varepsilon})$ as $t\to+\infty$.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "Means of powers (or moments) of the zeta function", first displayed formula.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem lindelof_iff_moments :
    RiemannVonMangoldt.LindelofHypothesis ↔
      ∀ k : ℕ, 0 < k → ∀ ε : ℝ, 0 < ε →
        (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k))
          =O[atTop] (fun T : ℝ => T ^ ε) := by sorry

end LindelofHypothesis
