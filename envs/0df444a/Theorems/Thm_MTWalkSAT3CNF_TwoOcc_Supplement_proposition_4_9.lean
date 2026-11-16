-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_proposition_4_9
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.proposition_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:59:17.648854+00:00
-- url     : https://prove2.me/theorems/40cc2687-9a6b-43cc-98b2-c293fa06ba75
-- title:
--   Proposition 4.9 — WalkSAT lower bound for F_L from uniform initialization
-- statement:
--   Let $L\ge40$ be an integer and let $R$ be any legal history-adaptive clause-selection rule for WalkSAT on $F_L$. Under independent uniform initialization,
--
--   $$E[T_{WS}(F_L)]\ge\frac{(3/2)^L-1}{9}\left(\frac{15}{16}\right)^{3(L-1)}.$$
--
--   The expectation includes all subsequent random choices and may be infinite. The bound applies to every adaptive rule, as established by the proof on pp. 22–23.
--
--   Differences from the source:
--   - encoding: one-based branch/module indices and indexed conjunctions → zero-based Fin indices and a bijective reindexing of the constructed clause family, retaining duplicate clauses; reason: only variable and clause labels change; every source instance is preserved
--   - encoding: possibly infinite algorithmic hitting times and expectations → published ℕ∞ hitting times and ℝ≥0∞ lower integrals; finite real bounds embedded by ENNReal.ofReal; reason: preserves infinite runtimes and is equivalent to each displayed nonnegative bound
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Proposition 4.9, p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Hard

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem proposition_4_9 (L : ℕ) (hL : 40 ≤ L)
    (R : WSRule (hardFormula L hL)) :
    ENNReal.ofReal ((((3:ℝ)/2)^L-1)/9 * ((15:ℝ)/16)^(3*(L-1))) ≤
      wsExpectedTime (hardFormula L hL) R (uniformAssignment (HardVar L)) := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
