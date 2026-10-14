-- Prove2me | Theorems.Thm_LindelofHypothesis_second_moment_asymptotic
-- name    : LindelofHypothesis.second_moment_asymptotic
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:49:08.629989+00:00
-- url     : https://prove2.me/theorems/b0440d60-b855-4288-ba7b-00d9a486ef1d
-- title:
--   Second moment asymptotic $\int_0^T|\zeta(\tfrac12+it)|^{2}dt=T(c_{1,0}\log T+c_{1,1})+o(T)$ (Littlewood)
-- statement:
--   There are real constants $c_{1,0},c_{1,1}$ such that
--   $$\int_0^T\left|\zeta\!\left(\tfrac12+it\right)\right|^{2}dt=T\sum_{j=0}^{1}c_{1,j}\,(\log T)^{1-j}+o(T)\qquad(T\to\infty).$$
--
--   This is the case $k=1$ of the conjectured asymptotic $\int_0^T|\zeta(\tfrac12+it)|^{2k}dt=T\sum_{j=0}^{k^2}c_{k,j}(\log T)^{k^2-j}+o(T)$, proved by Littlewood.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "Means of powers (or moments) of the zeta function", second displayed formula with k = 1 ("This has been proved by Littlewood for k = 1").

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem second_moment_asymptotic :
    ∃ c : ℕ → ℝ,
      (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) -
          T * ∑ j ∈ Finset.range 2, c j * Real.log T ^ (1 - j))
        =o[atTop] (fun T : ℝ => T) := by sorry

end LindelofHypothesis
