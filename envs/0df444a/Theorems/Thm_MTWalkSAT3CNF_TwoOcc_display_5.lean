-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_display_5
-- name    : MTWalkSAT3CNF.TwoOcc.display_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:25.628626+00:00
-- url     : https://prove2.me/theorems/0cb88e19-cbfc-423f-aff5-3e51a21fe5b6
-- title:
--   §3.2 display (5) — WalkSAT in the opposite-sign case: $\mathbb E[T_{WS}]\le4m$
-- statement:
--   Let $F=(C_1,\dots,C_m)$ be a 3-CNF formula with $\Delta(F)\le2$ in which every variable occurring twice has one positive and one negative occurrence. From every initial assignment $X_0$ and under every adaptive clause-selection rule, WalkSAT satisfies
--
--   $$\mathbb E[T_{WS}]\le 4m .$$
--
--   The general case (Theorem 3.4) is reduced to this one by same-sign splitting (Proposition 3.3).
--
--   Differences from the source:
--   - reading: an adaptive rule may depend on the history through time t but not on future random choices → a family of Markov kernels from the history (all past states, including the record of past choices) to a choice, possibly randomized; reason: the paper's uniform rule is randomized and is an instance of "every adaptive rule" in Theorems 3.1 and 3.4 (proof of Theorem 1.1, p. 11), so the class contains randomized rules; deterministic rules are the Dirac case
--   - encoding: the running time T and its expectation → an ℕ∞-valued hitting time on trajectories of the Ionescu–Tulcea trajectory law, expectation as lintegral in ℝ≥0∞; reason: Lean convention; same quantity, with no integrability assumption
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), §3.2, display (5), p. 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_WalkSAT

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc

/-- §3.2 display (5), p. 17: in the opposite-sign case with `Δ(F) ≤ 2`, WalkSAT satisfies
`E[T_WS] ≤ 4m` from every initial assignment and under every adaptive rule. -/
theorem display_5 {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) (hopp : OppositeSign F) (X₀ : V → Bool) (R : WSRule F) :
    wsExpectedTime F R (Measure.dirac X₀) ≤ 4 * (m : ℝ≥0∞) := by sorry

end MTWalkSAT3CNF.TwoOcc
