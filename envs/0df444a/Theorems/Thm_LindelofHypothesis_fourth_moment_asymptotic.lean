-- Prove2me | Theorems.Thm_LindelofHypothesis_fourth_moment_asymptotic
-- name    : LindelofHypothesis.fourth_moment_asymptotic
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:49:37.481344+00:00
-- url     : https://prove2.me/theorems/e2d2a6ee-e63c-421f-b525-5a6b0eb606ae
-- title:
--   Fourth moment asymptotic $\int_0^T|\zeta(\tfrac12+it)|^{4}dt=T\sum_{j=0}^{4}c_{2,j}(\log T)^{4-j}+o(T)$ (Heath-Brown)
-- statement:
--   There are real constants $c_{2,0},\dots,c_{2,4}$ such that
--   $$\int_0^T\left|\zeta\!\left(\tfrac12+it\right)\right|^{4}dt=T\sum_{j=0}^{4}c_{2,j}\,(\log T)^{4-j}+o(T)\qquad(T\to\infty).$$
--
--   This is the case $k=2$ of the conjectured moment asymptotic, proved by Heath-Brown (extending Ingham, who found the leading term).
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "Means of powers (or moments) of the zeta function", second displayed formula with k = 2 ("and by Heath-Brown for k = 2 (extending a result of Ingham who found the leading term)").

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem fourth_moment_asymptotic :
    ∃ c : ℕ → ℝ,
      (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 4) -
          T * ∑ j ∈ Finset.range 5, c j * Real.log T ^ (4 - j))
        =o[atTop] (fun T : ℝ => T) := by sorry

end LindelofHypothesis
