-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_cached_solve_count
-- name    : NearlyOptimalPPR.Computation.recursive_cached_solve_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:01:09.172004+00:00
-- url     : https://prove2.me/theorems/14cbe623-1227-46f4-bfeb-84a3e755963b
-- title:
--   Finite-prefix cached-solve count for recursive PageRank
-- statement:
--   There is a positive absolute constant $C$ such that every created recursive PageRank call satisfies
--
--   $$\operatorname{cachedSolves}\le C\bigl(2+\log(2/\varepsilon)+\ell\bigr)^4N$$
--
--   at every finite reachable prefix, where $N$ is its scale. The input graph is finite and undirected with a nonisolated seed, $0<\alpha\le1/2$, and $0<\varepsilon\le1$. The same constant works over primitive models, depths, schedules, and calls.
--
--   Cached solves occur at leaves. The estimate is the cached-solve counting part of the proof of Lemma 4.4. It counts actual guarded solver events and assumes no termination premise.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its leaf cached-solve amortization pp.28–29; Algorithms 6–9.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
attribute [local instance] Classical.propDecidable

theorem NearlyOptimalPPR.Computation.recursive_cached_solve_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
      (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
      ∀ (t id : ℕ) (info : CallInformation),
        (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).information id=some info →
          (((Finset.range t).filter (fun k => cachedSolveEvent g
            (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule k) id)).card : ℝ) ≤
              overhead C 4 ε ℓ*info.scale := by sorry
