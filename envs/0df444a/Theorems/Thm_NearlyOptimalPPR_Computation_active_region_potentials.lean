-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_active_region_potentials
-- name    : NearlyOptimalPPR.Computation.active_region_potentials
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:37:33.311313+00:00
-- url     : https://prove2.me/theorems/6299c658-7c20-49ba-9f4f-87a52351dfc2
-- title:
--   Lemma 3.7 — Connected active region and bounded potentials
-- statement:
--   Let $G$ be a finite simple unweighted undirected graph with a nonisolated seed $s$, $0<\alpha\le1/2$, and a root threshold $0<q\le1$. Write $N=1/q$. Consider any finite prefix of the operational recursive algorithm, at any depth and any legal fixed or balanced block schedule, with shared potential $x$ and root active region $H$.
--
--   Whenever $H$ is nonempty, it contains $s$ and its induced graph is connected. If a source-component vertex remains outside $H$, then
--
--   $$0\le x_v\le3N\qquad\text{for every vertex }v.$$
--
--   This is the uniform-threshold form used by the recursive proof as well as the nonrecursive routine: it specializes to $q=\varepsilon/96$ and to $q_0=\varepsilon/(32\kappa_0)$. The operational completion rule detects a fully explored source component by the maintained boundary-edge count, performs its charged principal solve, and returns the exact answer before further local operations.
--
--   The bound supplies the full range of potentials needed for the coordinate-doubling count. No connectedness or potential bound is assumed in the initial state.
--
--   Differences from the source:
--   - generalization: the nonrecursive threshold q=epsilon/96 and the recursive root threshold q_0 → every root threshold 0<q<=1 with N=1/q and every depth/block schedule; reason: the state argument uses only the root identity, activation cap, nonnegative increments and prioritized completion; both source thresholds specialize to this range
--   - encoding: H is a proper subset of the source component → there exists a vertex reachable from s outside H; reason: the separately concluded connectedness and inclusion of s put the active region in that component
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Lemma 3.7 pp.14–15; recursive invocation §5.3 p.28

import Mathlib
import Definitions.Def_NearlyOptimalPPR_Computation_recursive

set_option autoImplicit false

open Finset Matrix

namespace NearlyOptimalPPR.Computation

/-- Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Lemma 3.7 pp.14--15 and its recursive invocation §5.3 p.28.
Uniform q specializes both to epsilon/96 and epsilon/(32*kappa_0). -/
theorem active_region_potentials (m : SolveModel) (n : ℕ) (g : InputGraph n)
    (s : Fin n) (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
    (hα : 0 < α ∧ α ≤ 1 / 2) (hq : 0 < q ∧ q ≤ 1)
    (hs : 0 < g.graph.degree s) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    let H := (st.frames 0).active
    (H.Nonempty → s ∈ H ∧ (g.graph.induce (↑H : Set (Fin n))).Connected) ∧
    ((∃ v, g.graph.Reachable s v ∧ v ∉ H) → ∀ v, 0 ≤ st.x v ∧ st.x v ≤ 3 / q) := by sorry

end NearlyOptimalPPR.Computation
