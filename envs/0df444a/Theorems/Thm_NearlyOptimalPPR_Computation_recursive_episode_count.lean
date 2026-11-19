-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_episode_count
-- name    : NearlyOptimalPPR.Computation.recursive_episode_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:28:35.452938+00:00
-- url     : https://prove2.me/theorems/cf48323c-77f1-4b12-bffe-02b74da63ac0
-- title:
--   Finite-prefix episode count for recursive PageRank
-- statement:
--   There is a positive absolute constant $C$ such that every created recursive PageRank call satisfies, at every finite prefix,
--
--   $$\operatorname{episodes}\le C\bigl(2+\log(2/\varepsilon)+\ell\bigr)^4\frac Nb.$$
--
--   Here $N$ and $b$ are the call's scale and block size, the depth is $\ell$, and $0<\varepsilon\le1$. The finite undirected input graph has a nonisolated seed and $0<\alpha\le1/2$. The same constant works over all graphs, primitive models, depths, schedules, and calls.
--
--   This is the episode-count component of Lemma 4.4. It counts actual episode entries in finite reachable prefixes and assumes no eventual termination.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its finite-prefix episode-counting argument pp.28–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_episode_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
      (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
      ∀ (t id : ℕ) (info : CallInformation),
        (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).information id=some info →
          ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).episodes id : ℝ) ≤
            overhead C 4 ε ℓ*info.scale/info.block := by sorry
