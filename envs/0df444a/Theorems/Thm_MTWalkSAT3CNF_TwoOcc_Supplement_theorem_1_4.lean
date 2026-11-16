-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_theorem_1_4
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:06:40.073404+00:00
-- url     : https://prove2.me/theorems/569012c0-1ef9-48de-93da-81ab7920f940
-- title:
--   Theorem 1.4 — A growing satisfiable family with exponential WalkSAT and linear Moser–Tardos time
-- statement:
--   There exists an infinite family of satisfiable formulas $F_j=F(G_j)$ obtained from an explicitly constructible family of §6 graphs. Their clause counts are $m_j=1846|V_j|$ and tend to infinity. Under uniform clause selection and independent uniform initialization of all variables, with $\gamma=\tfrac18\log_2(486/451)>0$,
--
--   $$E[T_{MT}(F_j)]\le\frac{2763}{1846}m_j\quad\text{for every }j,$$
--   $$E[T_{WS}(F_j)]\ge2^{(\gamma/1846)m_j-2}\quad\text{for all sufficiently large }j.$$
--
--   These are the proof-supplied constants for the full exponential-WS and linear-MT separation. The graphs, formula clauses and process laws are constructed independently of any runtime conclusion.
--
--   Differences from the source:
--   - encoding: possibly infinite algorithmic hitting times and expectations → published ℕ∞ hitting times and ℝ≥0∞ lower integrals; finite real bounds embedded by ENNReal.ofReal; reason: preserves infinite runtimes and is equivalent to each displayed nonnegative bound
--   - encoding: existence of formulas with diverging clause count and asymptotic separation → the constructed graph-code/formula family with m=1846N, the exact MT coefficient and eventual WS exponent supplied by the proof; reason: the source proves these constants on pp. 39 and 42–43; finite graph labels use j+1 and both asymptotic conclusions follow
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Theorem 1.4, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Expander

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem theorem_1_4 :
    0 < gamma ∧ ∃ f : ℕ → ℕ × ℕ,
      ExplicitExpanderFamily f ∧
      Filter.Tendsto (fun j => Fintype.card (ExpIndex (graphOfCode (f j))))
        Filter.atTop Filter.atTop ∧
      (∀ j : ℕ,
        Satisfiable (expFormula (graphOfCode (f j))) ∧
        Fintype.card (ExpIndex (graphOfCode (f j))) = 1846*(f j).1 ∧
        (cnfSystem (expFormula (graphOfCode (f j)))).expectedTime
          (uniformRuleMT (expFormula (graphOfCode (f j)))) ≤
          ENNReal.ofReal ((2763/1846:ℝ)*Fintype.card (ExpIndex (graphOfCode (f j))))) ∧
      (∀ᶠ j in Filter.atTop,
        ENNReal.ofReal ((2:ℝ)^((gamma/1846)*Fintype.card (ExpIndex (graphOfCode (f j)))-2)) ≤
          wsExpectedTime (expFormula (graphOfCode (f j)))
            (uniformRuleWS (expFormula (graphOfCode (f j))))
            (uniformAssignment (ExpVar (f j).1))) := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
