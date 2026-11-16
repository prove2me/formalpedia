-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_proposition_4_12
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.proposition_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:01:41.498896+00:00
-- url     : https://prove2.me/theorems/9470c8ad-d97c-433f-8421-79833f31ceee
-- title:
--   Proposition 4.12 — Uniform upper bound for both formulas, both algorithms and every initial assignment
-- statement:
--   Let $L\ge40$, choose either $F_L$ or $\widehat F_L$, and let $n=12L^2-3L-6$ be its number of variables. For every fixed initial assignment $\sigma$ and every legal history-adaptive clause-selection rule, both algorithms satisfy
--
--   $$E_\sigma[T_A(F)]\le3n+75(5^{3L-1}-1),\qquad A\in\{WS,MT\}.$$
--
--   The bound is on the untruncated expected hitting time. It supplies a uniform upper bound for both hard families and every initial assignment.
--
--   Differences from the source:
--   - encoding: one-based branch/module indices and indexed conjunctions → zero-based Fin indices and a bijective reindexing of the constructed clause family, retaining duplicate clauses; reason: only variable and clause labels change; every source instance is preserved
--   - encoding: possibly infinite algorithmic hitting times and expectations → published ℕ∞ hitting times and ℝ≥0∞ lower integrals; finite real bounds embedded by ENNReal.ofReal; reason: preserves infinite runtimes and is equivalent to each displayed nonnegative bound
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Proposition 4.12, p. 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Hard

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem proposition_4_12 (L : ℕ) (hL : 40 ≤ L) (b : Bool)
    (σ : HardVar L → Bool) :
    (∀ R : WSRule (familyFormula L hL b),
      wsExpectedTime (familyFormula L hL b) R (Measure.dirac σ) ≤
        ENNReal.ofReal (3*(Fintype.card (HardVar L):ℝ) + 75*((5:ℝ)^(3*L-1)-1))) ∧
    (∀ R : MTRule (cnfSystem (familyFormula L hL b)),
      mtMeanFrom (familyFormula L hL b) R σ ≤
        ENNReal.ofReal (3*(Fintype.card (HardVar L):ℝ) + 75*((5:ℝ)^(3*L-1)-1))) := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
