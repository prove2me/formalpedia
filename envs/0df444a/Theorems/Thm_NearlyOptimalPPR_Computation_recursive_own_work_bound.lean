-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_own_work_bound
-- name    : NearlyOptimalPPR.Computation.recursive_own_work_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:05:44.661926+00:00
-- url     : https://prove2.me/theorems/a72abb9c-cdf3-495f-b6e8-24e80f1a1050
-- title:
--   Own-work bound for a recursive PageRank call
-- statement:
--   Fix the exact-solve primitive model. There are positive constants $C$ and a positive integer $c$ such that every created call, at every finite prefix, satisfies
--
--   $$\operatorname{ownWork}\le C\bigl(2+\log(2/\varepsilon)+\ell\bigr)^c
--   \left(\frac{N^2}{b}+\mathbf1_{j=\ell}Nb\right).$$
--
--   Here $j$, $N$, and $b$ are its level, scale, and block size. Own work counts the actual debits produced by this call, excluding descendant debits. The input graph is finite and undirected with a nonisolated seed, $0<\alpha\le1/2$, and $0<\varepsilon\le1$.
--
--   This is the nonrecursive cost component of Lemma 4.4. It includes adjacency-row discovery, control visits, assembly and propagation, and exact solves, including completed budget-crossing updates. The constants depend only on the primitive model; neither closure nor termination is assumed.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its own-work accounting pp.28–29; Algorithms 6–9.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem NearlyOptimalPPR.Computation.recursive_own_work_bound (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
        (T id : ℕ) (info : CallInformation),
        (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
        (run T).information id=some info →
        (∑ k ∈ range T, ownStepCharge m g α ℓ (run k) id) ≤
          ENNReal.ofReal (overhead C c ε ℓ*(info.scale^2/info.block+
            if info.level=ℓ then info.scale*info.block else 0)) := by sorry
