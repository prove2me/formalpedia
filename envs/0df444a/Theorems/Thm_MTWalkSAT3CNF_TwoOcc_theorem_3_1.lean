-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_theorem_3_1
-- name    : MTWalkSAT3CNF.TwoOcc.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:20.51631+00:00
-- url     : https://prove2.me/theorems/e43d1fed-ab0b-427e-b012-0916a9a36a4c
-- title:
--   Theorem 3.1 — Moser–Tardos with $\Delta(F)\le2$: $\mathbb E[T_{MT}]\le m/2\le n/3$
-- statement:
--   Let $F=(C_1,\dots,C_m)$ be a 3-CNF formula with $\Delta(F)\le2$. Starting from the uniform product distribution, Moser–Tardos satisfies
--
--   $$\mathbb E[T_{MT}]\le\frac m2\le\frac n3,$$
--
--   where $n$ is the number of variables occurring in $F$. The bound holds for every adaptive rule for selecting an unsatisfied clause.
--
--   This is the Moser–Tardos half of Theorem 1.1, obtained in the paper from Pegden's cluster-expansion criterion (Theorem 3.2) with $\mu=1/2$ for every clause.
--
--   Differences from the source:
--   - reading: an adaptive rule may depend on the history through time t but not on future random choices → a family of Markov kernels from the history (all past states, including the record of past choices) to a choice, possibly randomized; reason: the paper's uniform rule is randomized and is an instance of "every adaptive rule" in Theorems 3.1 and 3.4 (proof of Theorem 1.1, p. 11), so the class contains randomized rules; deterministic rules are the Dirac case
--   - encoding: the uniform product distribution on {0,1}^V with V the variables of F → the product of fair bits over a variable type that may also contain non-occurring variables; reason: non-occurring variables never enter a bad event and are never resampled, so T_MT has the same law
--   - encoding: the running time T and its expectation → an ℕ∞-valued hitting time on trajectories of the Ionescu–Tulcea trajectory law, expectation as lintegral in ℝ≥0∞; reason: Lean convention; same quantity, with no integrability assumption
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), Theorem 3.1, p. 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_MoserTardos

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc

/-- Theorem 3.1, p. 11: for a 3-CNF formula with `Δ(F) ≤ 2`, Moser–Tardos started from the
uniform product distribution satisfies `E[T_MT] ≤ m/2 ≤ n/3` under every adaptive rule, where
`n` is the number of variables occurring in `F`. -/
theorem theorem_3_1 {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) (R : MTRule (cnfSystem F)) :
    (cnfSystem F).expectedTime R ≤ (m : ℝ≥0∞) / 2 ∧
    (m : ℝ) / 2 ≤ (numOccVars F : ℝ) / 3 := by sorry

end MTWalkSAT3CNF.TwoOcc
