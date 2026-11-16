-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_theorem_4_1
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:02:44.359095+00:00
-- url     : https://prove2.me/theorems/dcb0fae2-0665-41d5-9342-7d85bdcfaa70
-- title:
--   Theorem 4.1 — The full occurrence-three hard family theorem, including both families and adaptive rules
-- statement:
--   For every integer $L\ge40$, the constructed formulas $F_L$ and $\widehat F_L$ are satisfiable 3-CNF formulas with three distinct variables in every clause and maximum variable occurrence exactly three. They both use $n=12L^2-3L-6$ occurring variables; their clause counts are respectively $12L^2-6L-5$ and $12L^2-3L-6$. For either formula with $m$ clauses, every legal history-adaptive rule, and either algorithm,
--
--   $$2^{\sqrt m/32}\le E[T_A(F)]\le2^{3\sqrt m},\qquad A\in\{WS,MT\}.$$
--
--   These displayed bounds use independent uniform initialization. The upper bound also holds from every fixed initial assignment. Moreover, $F_L$ has no repeated clauses and every variable in $\widehat F_L$ occurs once positively and twice negatively. This is the full occurrence-three companion theorem, including the scope paragraph immediately following its statement, and includes the introduction's Theorem 1.2.
--
--   Differences from the source:
--   - encoding: one-based branch/module indices and indexed conjunctions → zero-based Fin indices and a bijective reindexing of the constructed clause family, retaining duplicate clauses; reason: only variable and clause labels change; every source instance is preserved
--   - encoding: possibly infinite algorithmic hitting times and expectations → published ℕ∞ hitting times and ℝ≥0∞ lower integrals; finite real bounds embedded by ENNReal.ofReal; reason: preserves infinite runtimes and is equivalent to each displayed nonnegative bound
--   - encoding: Θ(L²) clause counts with exact values given in (12) and (31) → the two exact clause counts and the exact common occurring-variable count; reason: the source gives these equalities; they imply the stated quadratic growth
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Theorem 4.1, p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Hard

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem theorem_4_1 (L : ℕ) (hL : 40 ≤ L) :
    Fintype.card (HardVar L) = 12*L^2-3*L-6 ∧
    NoRepeated (hardFormula L hL) ∧
    (∀ v, signedOcc (completedFormula L hL) v true = 1 ∧
      signedOcc (completedFormula L hL) v false = 2) ∧
    ∀ b : Bool,
      Satisfiable (familyFormula L hL b) ∧ MaxOccThree (familyFormula L hL b) ∧
      (∀ i, Function.Injective ((familyFormula L hL b) i).var) ∧
      Fintype.card (FamilyIndex L b) = (if b then 12*L^2-3*L-6 else 12*L^2-6*L-5) ∧
      numOccVars (familyFormula L hL b) = 12*L^2-3*L-6 ∧
      (∀ R : WSRule (familyFormula L hL b),
        ENNReal.ofReal ((2:ℝ)^(Real.sqrt (Fintype.card (FamilyIndex L b):ℝ)/32)) ≤
          wsExpectedTime (familyFormula L hL b) R (uniformAssignment (HardVar L)) ∧
        wsExpectedTime (familyFormula L hL b) R (uniformAssignment (HardVar L)) ≤
          ENNReal.ofReal ((2:ℝ)^(3*Real.sqrt (Fintype.card (FamilyIndex L b):ℝ)))) ∧
      (∀ R : MTRule (cnfSystem (familyFormula L hL b)),
        ENNReal.ofReal ((2:ℝ)^(Real.sqrt (Fintype.card (FamilyIndex L b):ℝ)/32)) ≤
          (cnfSystem (familyFormula L hL b)).expectedTime R ∧
        (cnfSystem (familyFormula L hL b)).expectedTime R ≤
          ENNReal.ofReal ((2:ℝ)^(3*Real.sqrt (Fintype.card (FamilyIndex L b):ℝ)))) ∧
      (∀ (σ : HardVar L → Bool) (R : WSRule (familyFormula L hL b)),
        wsExpectedTime (familyFormula L hL b) R (Measure.dirac σ) ≤
          ENNReal.ofReal ((2:ℝ)^(3*Real.sqrt (Fintype.card (FamilyIndex L b):ℝ)))) ∧
      (∀ (σ : HardVar L → Bool) (R : MTRule (cnfSystem (familyFormula L hL b))),
        mtMeanFrom (familyFormula L hL b) R σ ≤
          ENNReal.ofReal ((2:ℝ)^(3*Real.sqrt (Fintype.card (FamilyIndex L b):ℝ)))) := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
