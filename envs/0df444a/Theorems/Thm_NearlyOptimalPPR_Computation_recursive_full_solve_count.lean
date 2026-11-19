-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_full_solve_count
-- name    : NearlyOptimalPPR.Computation.recursive_full_solve_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:21:18.379129+00:00
-- url     : https://prove2.me/theorems/ed39d2ef-c9e7-46e2-863b-ec0b48f2cd3c
-- title:
--   Finite-prefix full-solve count in recursive PageRank
-- statement:
--   There is a positive absolute constant $C$ such that every recursive PageRank call created on a valid input obeys the following bound at every finite prefix:
--
--   $$\#\{\text{full solves of the call}\}\le C\bigl(2+\log(2/\varepsilon)+\ell\bigr)^3\frac{N}{b}.$$
--
--   Here $N\ge1$ and $b\ge1$ are the call's scale and block size, $\ell$ is the depth, $0<\varepsilon\le1$, and the teleportation parameter satisfies $0<\alpha\le1/2$. The graph is finite and undirected and the seed is nonisolated. The same constant works across graphs, calls, depths, primitive solve models, and block schedules.
--
--   This is the full-solve event-count component of Lemma 4.4. It holds for finite prefixes, so it does not use termination as a premise.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18, Lemmas 5.7–5.8 and the finite-prefix counting proof pp.26–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_full_solve_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
      (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
      ∀ (t id : ℕ) (info : CallInformation),
        (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).information id=some info →
          ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).fullSolves id : ℝ) ≤
            overhead C 3 ε ℓ*info.scale/info.block := by sorry
