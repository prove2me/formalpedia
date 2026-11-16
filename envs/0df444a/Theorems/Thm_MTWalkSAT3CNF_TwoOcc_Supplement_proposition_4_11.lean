-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_proposition_4_11
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.proposition_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:00:54.469919+00:00
-- url     : https://prove2.me/theorems/23062a5a-d544-4fc9-87fc-d8869a19192c
-- title:
--   Proposition 4.11 — Both lower bounds survive the completion to F̂_L
-- statement:
--   For every integer $L\ge40$, the completed formula $\widehat F_L$ satisfies both lower bounds, each under every legal history-adaptive clause-selection rule and independent uniform initialization:
--
--   $$E[T_{WS}(\widehat F_L)]\ge\frac{(3/2)^L-1}{9}\left(\frac{15}{16}\right)^{3(L-1)},$$
--   $$E[T_{MT}(\widehat F_L)]\ge\frac{2((3/2)^L-1)}{27}\left(\frac{15}{16}\right)^{3(L-1)}.$$
--
--   Both estimates are expanded explicitly. The two identical completion clauses retain separate indices and no variable is added.
--
--   Differences from the source:
--   - encoding: one-based branch/module indices and indexed conjunctions → zero-based Fin indices and a bijective reindexing of the constructed clause family, retaining duplicate clauses; reason: only variable and clause labels change; every source instance is preserved
--   - encoding: possibly infinite algorithmic hitting times and expectations → published ℕ∞ hitting times and ℝ≥0∞ lower integrals; finite real bounds embedded by ENNReal.ofReal; reason: preserves infinite runtimes and is equivalent to each displayed nonnegative bound
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Proposition 4.11, p. 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Hard

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem proposition_4_11 (L : ℕ) (hL : 40 ≤ L) :
    (∀ R : WSRule (completedFormula L hL),
      ENNReal.ofReal ((((3:ℝ)/2)^L-1)/9 * ((15:ℝ)/16)^(3*(L-1))) ≤
        wsExpectedTime (completedFormula L hL) R (uniformAssignment (HardVar L))) ∧
    (∀ R : MTRule (cnfSystem (completedFormula L hL)),
      ENNReal.ofReal (2*(((3:ℝ)/2)^L-1)/27 * ((15:ℝ)/16)^(3*(L-1))) ≤
        (cnfSystem (completedFormula L hL)).expectedTime R) := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
