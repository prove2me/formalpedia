-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_theorem_3_4
-- name    : MTWalkSAT3CNF.TwoOcc.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:37.886569+00:00
-- url     : https://prove2.me/theorems/f9bea98a-a4fc-41d2-9fa2-1b61f4229456
-- title:
--   Theorem 3.4 — WalkSAT with $\Delta(F)\le2$: $\mathbb E[T_{WS}]\le4m\le\frac83n$
-- statement:
--   Let $F=(C_1,\dots,C_m)$ be a 3-CNF formula with $\Delta(F)\le2$. WalkSAT satisfies
--
--   $$\mathbb E[T_{WS}]\le 4m\le\frac83\,n$$
--
--   from every initial assignment, where $n$ is the number of variables occurring in $F$. The bound holds for every adaptive rule for selecting an unsatisfied clause.
--
--   This is the WalkSAT half of Theorem 1.1. Unlike displays (2)–(5), no sign condition is assumed.
--
--   Differences from the source:
--   - reading: an adaptive rule may depend on the history through time t but not on future random choices → a family of Markov kernels from the history (all past states, including the record of past choices) to a choice, possibly randomized; reason: the paper's uniform rule is randomized and is an instance of "every adaptive rule" in Theorems 3.1 and 3.4 (proof of Theorem 1.1, p. 11), so the class contains randomized rules; deterministic rules are the Dirac case
--   - encoding: the running time T and its expectation → an ℕ∞-valued hitting time on trajectories of the Ionescu–Tulcea trajectory law, expectation as lintegral in ℝ≥0∞; reason: Lean convention; same quantity, with no integrability assumption
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), Theorem 3.4, p. 13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_WalkSAT

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc

/-- Theorem 3.4, p. 13: for a 3-CNF formula with `Δ(F) ≤ 2`, WalkSAT satisfies
`E[T_WS] ≤ 4m ≤ (8/3) n` from every initial assignment and under every adaptive rule, where `n`
is the number of variables occurring in `F`. -/
theorem theorem_3_4 {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) (X₀ : V → Bool) (R : WSRule F) :
    wsExpectedTime F R (Measure.dirac X₀) ≤ 4 * (m : ℝ≥0∞) ∧
    4 * (m : ℝ) ≤ 8 / 3 * (numOccVars F : ℝ) := by sorry

end MTWalkSAT3CNF.TwoOcc
