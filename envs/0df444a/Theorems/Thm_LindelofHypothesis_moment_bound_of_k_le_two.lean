-- Prove2me | Theorems.Thm_LindelofHypothesis_moment_bound_of_k_le_two
-- name    : LindelofHypothesis.moment_bound_of_k_le_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:48:22.068091+00:00
-- url     : https://prove2.me/theorems/8e0dcb9b-2ac5-4a6c-b97d-728bbd57f907
-- title:
--   Moment bound $\frac1T\int_0^T|\zeta(\tfrac12+it)|^{2k}dt=O(T^{\varepsilon})$ for $k=1,2$
-- statement:
--   For $k\in\{1,2\}$ and every real $\varepsilon>0$,
--   $$\frac1T\int_0^T\left|\zeta\!\left(\tfrac12+it\right)\right|^{2k}dt=O\!\left(T^{\varepsilon}\right)\qquad(T\to\infty).$$
--
--   These are the two cases of the moment formulation of the Lindelöf hypothesis that are known; the case $k=3$ is open.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "Means of powers (or moments) of the zeta function", sentence "This has been proved for k = 1 or 2".

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem moment_bound_of_k_le_two (k : ℕ) (hk : k = 1 ∨ k = 2) (ε : ℝ) (hε : 0 < ε) :
    (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k))
      =O[atTop] (fun T : ℝ => T ^ ε) := by sorry

end LindelofHypothesis
