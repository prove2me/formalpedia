-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_finite_prefix_counts
-- name    : NearlyOptimalPPR.Computation.recursive_finite_prefix_counts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:13:34.509065+00:00
-- url     : https://prove2.me/theorems/33fd0377-dc0e-480a-b5c2-06b1e8149232
-- title:
--   Finite-prefix counts and eventual closure of recursive PageRank calls
-- statement:
--   There is a positive absolute constant $C$ such that every created recursive PageRank call, at every finite prefix, satisfies
--
--   $$\operatorname{episodes},\ \operatorname{fullSolves}\le
--   C\bigl(2+\log(2/\varepsilon)+\ell\bigr)^4\frac{N}{b}.$$
--
--   Here $N$ and $b$ are the call's scale and block size. Every completed episode spawned at most one child, and the same bound holds for the child count in the current episode of an open call. Moreover, every call recorded at a finite prefix closes at some later finite prefix.
--
--   The graph is finite and undirected with a nonisolated seed, $0<\alpha\le1/2$, and $0<\varepsilon\le1$. The constant is uniform over input graphs, primitive solve models, block schedules, and depths. This is the event-count and termination part of Lemma 4.4; termination is a conclusion, not an execution premise.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its finite-prefix counts, termination argument, and work accounting pp.28–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem NearlyOptimalPPR.Computation.recursive_finite_prefix_counts :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      0 < ε → ε ≤ 1 → ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α : ℝ),
      0 < α → α ≤ 1/2 → 0 < g.graph.degree s → ∀ (t id : ℕ) (info : CallInformation),
      let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
      (run t).information id=some info →
        ((run t).episodes id : ℝ) ≤ overhead C 4 ε ℓ*info.scale/info.block ∧
        ((run t).fullSolves id : ℝ) ≤ overhead C 4 ε ℓ*info.scale/info.block ∧
        (∀ k ∈ (run t).episodeChildCounts id, k ≤ 1) ∧
        (∀ i ≤ (run t).top, ((run t).frames i).id=id → ((run t).frames i).childrenThisEpisode ≤ 1) ∧
        ∃ t' ≥ t, id ∈ (run t').closed := by sorry
