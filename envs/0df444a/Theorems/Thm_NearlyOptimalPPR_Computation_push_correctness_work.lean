-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_push_correctness_work
-- name    : NearlyOptimalPPR.Computation.push_correctness_work
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:38:57.78186+00:00
-- url     : https://prove2.me/theorems/7083db3c-399d-42c3-93c3-09aa1f6f492b
-- title:
--   Lemma 2.3 — Push correctness and work
-- statement:
--   There is an absolute constant $C>0$ such that for every finite simple unweighted undirected graph, every nonisolated seed $s$, and real $0<\alpha<1$, $0<\varepsilon\le1$, Algorithm 1 terminates with a nonnegative potential $z$ and its explicit output $\widehat\pi_s=\alpha Dz$. Its total charged work $W$, including queue work, graph queries, and output, satisfies
--
--   $$W\le\frac C{\alpha\varepsilon},\qquad 0\le e_s-Mz\le\varepsilon d,$$
--
--   and consequently
--
--   $$|\widehat\pi_s(v)-\pi_s(v)|\le\varepsilon d_v\qquad(v\in V).$$
--
--   Here $M=D-(1-\alpha)A$, all inequalities are coordinatewise, and the same constant works for all graph sizes, sources and parameters. The nonisolated-source convention is the standing one in §2; the goal handles an isolated seed separately and exactly.
--
--   For $\alpha>1/2$, this supplies the goal's remaining teleportation range with work at most $2C/\varepsilon$.
--
--   Differences from the source:
--   - encoding: Algorithm 1 with O(1/(alpha epsilon)) local work → the FIFO sparse operational implementation with one uniform work constant; reason: queue membership and touched-coordinate output realize the specified loop without any graph-size scan
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Lemma 2.3 and Algorithm 1 p.5; standing conventions p.4

import Mathlib
import Definitions.Def_NearlyOptimalPPR_Computation_push

set_option autoImplicit false

open Finset Matrix MeasureTheory
open scoped ENNReal

namespace NearlyOptimalPPR.Computation

/-- Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Lemma 2.3 and Algorithm 1 p.5; source and parameter conventions p.4. -/
theorem push_correctness_work :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α < 1 → 0 < ε → ε ≤ 1 → 0 < g.graph.degree s →
          pushWork g s α ε ≤ ENNReal.ofReal (C / (α * ε)) ∧
          ∃ t : ℕ,
            (pushRun g s α ε t).done = true ∧
            (∀ v, 0 ≤ (pushRun g s α ε t).z v) ∧
            (∀ v, 0 ≤ residual g.graph α s (pushRun g s α ε t).z v ∧
              residual g.graph α s (pushRun g s α ε t).z v ≤ ε * LocalPush.deg g.graph v) ∧
            outputVector (pushRun g s α ε t).output =
              potentialOutput g.graph α (pushRun g s α ε t).z ∧
            ACL g.graph α ε s (outputVector (pushRun g s α ε t).output) := by sorry

end NearlyOptimalPPR.Computation
