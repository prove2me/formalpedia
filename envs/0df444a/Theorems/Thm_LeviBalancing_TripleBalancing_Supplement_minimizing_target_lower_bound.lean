-- Prove2me | Theorems.Thm_LeviBalancing_TripleBalancing_Supplement_minimizing_target_lower_bound
-- name    : LeviBalancing.TripleBalancing.Supplement.minimizing_target_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:23:30.628947+00:00
-- url     : https://prove2.me/theorems/95f3ec43-1c67-47db-9701-c8723b0ac9e3
-- title:
--   Theorem 5.1 — the smallest minimizing-policy target bounds the optimal target below
-- statement:
--   Fix any period $s\in\{1,\ldots,T\}$ and any specified information state $f_s$ in the periodic-review model. Remaining demands have finite conditional means and may be arbitrarily correlated and nonstationary; lead time is any known nonnegative integer. Let $R^M(f_s)$ be the smallest minimizer of the §5.2 full-horizon marginal holding-plus-backlog target objective. Let $R^{OPT}(f_s)$ be an actual conditional optimal base-stock target, using optimal continuation over all feasible nonanticipatory future controls. Whenever these named targets are defined,
--
--   $$
--   R^M(f_s)\le R^{OPT}(f_s).
--   $$
--
--   Thus the minimizing policy supplies a lower bound on the optimal target, rather than the classical one-period myopic policy's upper bound.
--
--   **Formalization Note** The statement is rooted at each conditional information state, not merely almost surely from one initial distribution. Supplied targets carry their exact minimization and optimal-continuation properties; no desired comparison is included in those properties. The source presupposes these named levels. No smallest real minimizer exists when the target objective is constant, including after the last actionable period. Such undefined levels are not replaced by zero or excluded through strictly positive rates.
--
--   Differences from the source:
--   - encoding: for each period and information set, named smallest minimizing and optimal targets → an arbitrary conditional subproblem rooted at (s,f_s), with target-minimizer and genuine optimal-continuation witnesses; reason: local finite demand means are the stated conditional means; witnesses bind the objects the page names and do not assume their ordering
--   - reading: R^M and R^{OPT} are denoted for t=1,…,T → comparison whenever both named targets are defined, retaining every s in 1,…,T; reason: after T-L the target surrogate is constant and has no smallest real minimizer; zero-rate cases can have the same defect, so no default target or positivity restriction is introduced
--   - encoding: minimize marginal holding plus backlog for y≥x → minimize the target-level full-horizon holding-plus-backlog objective; reason: p. 298 explicitly removes a term independent of y on y≥x; this gives the same smallest target and action max(x,R^M)
--   - encoding: the optimal dynamic-programming target → optimality for the Bellman action with continuation over all feasible adapted future controls, and attainment; reason: the variational continuation unrolls the finite-horizon Bellman recursion and keeps the actual optimal problem, without restricting demand or comparator policies
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 298 (PDF 15), Theorem 5.1; optimal targets pp. 289–290 (PDF 6–7)

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Supplement_Targets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeviBalancing.TripleBalancing.Supplement
open LeviBalancing.DualBalancing

/-- Theorem 5.1, p. 298 (PDF 15), at any specified conditional information state. Named
source targets are witnessed by their actual minimization and optimal-continuation
properties. No target is assigned a default when its defining minimum has no least element.
The full period range is retained; after the last actionable date the surrogate is constant
and has no smallest real minimizer, so the source's named R^M is undefined there. -/
theorem minimizing_target_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (I : Instance) (s : ℤ)
    (hs : 1 ≤ s) (hsT : s ≤ (I.T : ℤ)) (M : ConditionalProblem Ω I s)
    (RM ROPT : ℝ) (hRM : IsSmallestMinimizingTarget M RM)
    (hROPT : IsOptimalBaseStockTarget M ROPT) : RM ≤ ROPT := by sorry

end LeviBalancing.TripleBalancing.Supplement
