-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_joint_solve_overhead
-- name    : NearlyOptimalPPR.Computation.recursive_joint_solve_overhead
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:40:37.625297+00:00
-- url     : https://prove2.me/theorems/aabf1251-978b-4938-a8ac-f11074e295ca
-- title:
--   Uniform overhead for a joint exact-solve update
-- statement:
--   Fix the exact-solve primitive model. There are positive constants $C$ and a positive integer $c$ such that every joint update on a domain $T$ contained in the root active region satisfies
--
--   $$\operatorname{jointCost}(T)\le
--   C\bigl(2+\log(2/\varepsilon)+\ell\bigr)^c\bigl(\operatorname{vol}(T)+1\bigr).$$
--
--   The bound holds at every finite reachable prefix, for a nonisolated seed, $0<\alpha<1$, and $0<\varepsilon\le1$. The constants depend only on the primitive model and work uniformly across graphs, schedules, and levels.
--
--   The charged update includes the exact primitive and the separately accounted sparse assembly, propagation, and key maintenance. The root-volume and stored-data bounds reduce its logarithmic factors to the displayed uniform polynomial overhead used in Lemma 4.4.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its discovery/control/solve work accounting pp.28–29; exact-SDDM convention Section 2 p.4; Algorithms 6–9.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem NearlyOptimalPPR.Computation.recursive_joint_solve_overhead (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ),
        (0 < α ∧ α < 1) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        ∀ T : Finset (Fin n), T ⊆ ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).frames 0).active →
          jointCost m g (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t) T ≤
            ENNReal.ofReal (overhead C c ε ℓ*((volumeNat g T : ℝ)+1)) := by sorry
