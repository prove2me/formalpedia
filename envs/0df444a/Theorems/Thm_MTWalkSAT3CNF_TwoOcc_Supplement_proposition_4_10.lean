-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_proposition_4_10
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.proposition_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:00:24.183047+00:00
-- url     : https://prove2.me/theorems/cd7162ac-f943-4eb0-92b3-9f1b86279674
-- title:
--   Proposition 4.10 — Moser–Tardos lower bound for F_L from uniform initialization
-- statement:
--   Let $L\ge40$ be an integer and let $R$ be any legal history-adaptive clause-selection rule for Moser–Tardos on $F_L$. Under independent uniform initialization,
--
--   $$E[T_{MT}(F_L)]\ge\frac{2((3/2)^L-1)}{27}\left(\frac{15}{16}\right)^{3(L-1)}.$$
--
--   Every clause resampling counts as an update, including one that changes no bit. Infinite expected hitting time is allowed. This is the MT counterpart of the WalkSAT lower bound.
--
--   Differences from the source:
--   - encoding: one-based branch/module indices and indexed conjunctions → zero-based Fin indices and a bijective reindexing of the constructed clause family, retaining duplicate clauses; reason: only variable and clause labels change; every source instance is preserved
--   - encoding: possibly infinite algorithmic hitting times and expectations → published ℕ∞ hitting times and ℝ≥0∞ lower integrals; finite real bounds embedded by ENNReal.ofReal; reason: preserves infinite runtimes and is equivalent to each displayed nonnegative bound
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Proposition 4.10, p. 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Hard

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem proposition_4_10 (L : ℕ) (hL : 40 ≤ L)
    (R : MTRule (cnfSystem (hardFormula L hL))) :
    ENNReal.ofReal (2*(((3:ℝ)/2)^L-1)/27 * ((15:ℝ)/16)^(3*(L-1))) ≤
      (cnfSystem (hardFormula L hL)).expectedTime R := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
