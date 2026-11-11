-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_theorem_1_1
-- name    : MTWalkSAT3CNF.TwoOcc.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:40.447276+00:00
-- url     : https://prove2.me/theorems/ec1dd5b2-aea4-4704-8583-f37bbb164105
-- title:
--   Theorem 1.1 — with $\Delta(F)\le2$, $\mathbb E[T_{MT}(F)]\le m/2$ and $\mathbb E[T_{WS}(F)]\le4m$
-- statement:
--   For every 3-CNF formula $F$ with $m$ clauses and $\Delta(F)\le2$,
--
--   $$\mathbb E[T_{MT}(F)]\le\frac m2,\qquad \mathbb E[T_{WS}(F)]\le4m .$$
--
--   Both algorithms start from the uniform distribution on assignments (independent unbiased bits) and select at each step one of the currently unsatisfied clauses uniformly at random; Moser–Tardos resamples the three variables of the chosen clause, WalkSAT flips the variable at a uniformly chosen position of it. $T_{MT}$ counts resampling steps and $T_{WS}$ counts flips until no clause is unsatisfied.
--
--   Together with the paper's Theorem 1.2 (exponential-in-$\sqrt m$ running times at $\Delta(F)\le3$), this locates the occurrence threshold for both algorithms between two and three.
--
--   Differences from the source:
--   - encoding: the uniform distribution on assignments of V = {x_1, …, x_n} → the product of fair bits over a variable type that may also contain non-occurring variables; reason: non-occurring variables never enter a clause, so both running times have the same law
--   - encoding: the uniform clause-selection rule → uniformRuleMT / uniformRuleWS: at each step the uniform distribution on Bad_F(X_t) (PMF.uniformOfFinset), as a rule on histories whose states record the last choice; reason: Lean convention; the chosen-index law is exactly uniform on Bad_F(X_t)
--   - encoding: the running time T and its expectation → an ℕ∞-valued hitting time on trajectories of the Ionescu–Tulcea trajectory law, expectation as lintegral in ℝ≥0∞; reason: Lean convention; same quantity, with no integrability assumption
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), Theorem 1.1, p. 6 (canonical conventions of §1.1, p. 6, and §2.2, p. 10). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_MoserTardos
import Definitions.Def_MTWalkSAT3CNF_TwoOcc_WalkSAT

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc

/-- Theorem 1.1, p. 6: for every 3-CNF formula `F` with `m` clauses and `Δ(F) ≤ 2`, both
algorithms started from the uniform distribution on assignments with the uniform
clause-selection rule satisfy `E[T_MT(F)] ≤ m/2` and `E[T_WS(F)] ≤ 4m`. -/
theorem theorem_1_1 {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) :
    (cnfSystem F).expectedTime (uniformRuleMT F) ≤ (m : ℝ≥0∞) / 2 ∧
    wsExpectedTime F (uniformRuleWS F) (uniformAssignment V) ≤ 4 * (m : ℝ≥0∞) := by sorry

end MTWalkSAT3CNF.TwoOcc
