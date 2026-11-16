-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_proposition_4_2
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:58:21.753811+00:00
-- url     : https://prove2.me/theorems/dc316cdf-acec-4e3a-96a1-16944cc4246d
-- title:
--   Proposition 4.2 — Structure and exact sizes of the hard family F_L
-- statement:
--   For every integer $L\ge40$, the formula $F_L$ of (7)–(11) is satisfiable, has no repeated clauses even after forgetting literal order, has maximum variable occurrence exactly three, and has three distinct variables in every clause. Its counts are
--
--   $$m=12L^2-6L-5,\qquad n=12L^2-3L-6.$$
--
--   The variable count is stated both for the constructed carrier and for variables that actually occur. This establishes the structural properties of the hard family.
--
--   Differences from the source:
--   - encoding: one-based branch/module indices and indexed conjunctions → zero-based Fin indices and a bijective reindexing of the constructed clause family, retaining duplicate clauses; reason: only variable and clause labels change; every source instance is preserved
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Proposition 4.2, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Hard

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem proposition_4_2 (L : ℕ) (hL : 40 ≤ L) :
    Satisfiable (hardFormula L hL) ∧ NoRepeated (hardFormula L hL) ∧
    MaxOccThree (hardFormula L hL) ∧
    (∀ i, Function.Injective ((hardFormula L hL) i).var) ∧
    Fintype.card (HardIndex L) = 12*L^2-6*L-5 ∧
    Fintype.card (HardVar L) = 12*L^2-3*L-6 ∧
    numOccVars (hardFormula L hL) = 12*L^2-3*L-6 := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
