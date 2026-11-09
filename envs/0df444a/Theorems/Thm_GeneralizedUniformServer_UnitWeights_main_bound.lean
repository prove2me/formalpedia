-- Prove2me | Theorems.Thm_GeneralizedUniformServer_UnitWeights_main_bound
-- name    : GeneralizedUniformServer.UnitWeights.main_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:30.440126+00:00
-- url     : https://prove2.me/theorems/1e4b6f7f-ffea-4b2a-9141-9ba0326d573c
-- title:
--   Theorem 1.1 — a randomized online algorithm with $\mathbb E[\mathrm{ALG}(\rho)]\le(k+1)\ln(2k)\cdot\mathrm{OPT}(\rho)$
-- statement:
--   Let $k\ge1$, let $M_1,\dots,M_k$ be uniform metric spaces with unit distances, finite or infinite, and let $a$ be an initial configuration. There is a randomized online algorithm, starting at $a$ and always moving to a configuration that serves the current request, such that for every finite request sequence $\rho$,
--   $$\mathbb E[\mathrm{ALG}(\rho)]\le(k+1)\ln(2k)\cdot\mathrm{OPT}(\rho),$$
--   where $\mathrm{OPT}(\rho)$ is the cost of an optimal offline solution that starts from $a$, and $\ln$ is the natural logarithm. There is no additive constant.
--
--   This is the paper's upper bound for unit weights; with the lower bound of Theorem 1.2 it determines the randomized competitive ratio of generalized $k$-server on uniform metrics up to a constant factor.
--
--   **Formalization Note** The algorithm is chosen after $k$, the spaces and $a$, and before the request sequence; it sees the past requests, its current configuration and the new request, and uses fresh randomness at each step. The expectation is over its joint trajectory law and is taken in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: configurations on pairwise disjoint spaces, finite request sequences and unit movement costs → dependent configurations indexed by `Fin k`, request lists with 0-based entries, finite schedules where used, and natural-valued Hamming costs and OPT; reason: tagged coordinates preserve each space, the list and schedule indices relabel the source times, and every unit-weight cost is a natural number, with OPT attained over the nonempty feasible set
--   - generalization: a randomized online algorithm (that serves every request) → a transition kernel that depends only on the past requests, its current configuration and the new request, and whose every possible move, from every history and configuration, serves the new request; reason: such a kernel is in particular a randomized online algorithm serving every request, so the Lean existence statement implies the source's
--   - encoding: $\mathbb E[\mathrm{ALG}(\rho)]\le(k+1)\ln(2k)\,\mathrm{OPT}(\rho)$ in $\mathbb R$ → the expectation in $[0,\infty]$ bounded by `ENNReal.ofReal` of the real right-hand side; reason: the right-hand side is nonnegative for $k\ge1$, so the inequalities are equivalent
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 3, Theorem 1.1 (proof p. 9); model p. 7–8, §2

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Online

namespace GeneralizedUniformServer.UnitWeights

/-- Theorem 1.1 (source p. 3): let `M₁, …, M_k` (`k ≥ 1`) be uniform metric spaces with unit
distances, finite or infinite, and `a` an initial configuration. There is a randomized online
algorithm, which always moves to a configuration serving the current request, such that for
every finite request sequence `ρ`, `E[ALG(ρ)] ≤ (k + 1) ln(2k) · OPT(ρ)`, where `OPT(ρ)` is
the cost of an optimal offline solution starting from `a`. -/
theorem main_bound {k : ℕ} [NeZero k] {M : Fin k → Type*} (a : Config M) :
    ∃ A : OnlineAlg M,
      (∀ (hist : List (Config M)) (x r y : Config M), y ∈ (A hist x r).support → Serves y r) ∧
      ∀ ρ : List (Config M),
        expectedCost A a ρ ≤
          ENNReal.ofReal (((k : ℝ) + 1) * Real.log (2 * (k : ℝ)) * (optCost a ρ : ℝ)) := by sorry

end GeneralizedUniformServer.UnitWeights
