-- Prove2me | Theorems.Thm_MaxEntTSP_Main_proposition_2_3
-- name    : MaxEntTSP.Main.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:09.583647+00:00
-- url     : https://prove2.me/theorems/2361dcd7-6612-4e9b-8654-30f02ac2ea2d
-- title:
--   Proposition 2.3 — Edmonds–Johnson O-join cut formulation
-- statement:
--   Let $F$ be a finite loopless graph with nonnegative edge costs and let $O$ have even cardinality. For every nonnegative $y$ satisfying $y(\delta_F(S))\ge1$ when $|S\cap O|$ is odd, there is an $O$-join $J\subseteq F$ with
--   $$c(J)\le\sum_{e\in F}c_e y_e.$$
--
--   Conversely, the incidence vector of every $O$-join satisfies all those cut constraints. Together these statements give equality between the minimum $O$-join cost and the LP optimum whenever either side is feasible, without assigning a junk value to an empty infimum.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, p. 6 (PDF 8), Proposition 2.3 and LP (3)

import Mathlib
import Definitions.Def_MaxEntTSP_Main_OJoin
import Definitions.Def_MetricGenerators_FewComponents_TJoin

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- Edmonds–Johnson integrality of the `O`-join cut formulation. -/
theorem proposition_2_3 (m : ℕ) (F : Finset (Sym2 (Fin m)))
    (hloop : ∀ e ∈ F, ¬ e.IsDiag)
    (c : Fin m → Fin m → ℝ) (hc : ∀ e ∈ F, 0 ≤ pairCost c e)
    (O : Finset (Fin m)) (hO : Even O.card) :
    (∀ y : Sym2 (Fin m) → ℝ, OJoinFeasible F O y →
      ∃ J : Finset (Sym2 (Fin m)),
        MetricGenerators.FewComponents.IsTJoin (MetricGenerators.FewComponents.edgeGraph F) O J ∧
        (∑ e ∈ J, pairCost c e) ≤ ∑ e ∈ F, pairCost c e * y e) ∧
    (∀ J : Finset (Sym2 (Fin m)),
      MetricGenerators.FewComponents.IsTJoin (MetricGenerators.FewComponents.edgeGraph F) O J →
      OJoinFeasible F O (fun e => if e ∈ J then 1 else 0)) := by sorry

end MaxEntTSP.Main
