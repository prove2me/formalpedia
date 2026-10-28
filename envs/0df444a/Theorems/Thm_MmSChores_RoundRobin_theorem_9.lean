-- Prove2me | Theorems.Thm_MmSChores_RoundRobin_theorem_9
-- name    : MmSChores.RoundRobin.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:27.946866+00:00
-- url     : https://prove2.me/theorems/83b8ec03-dd20-4d0e-be22-c35850329281
-- title:
--   Theorem 9 — greedy round-robin gives every agent at least (2 − 1/N)·MmS on chores, and the factor cannot be improved
-- statement:
--   Let $I=(\mathcal M,[N],(d_i)_{i\in[N]})$ be an instance with $N\ge 1$ agents and additive utilities over a finite set $\mathcal M$ of chores, and let
--   $$\mathrm{MmS}^N_{d_i}(\mathcal M)=\max_{(S_1,\dots,S_N)\in\Pi_N(\mathcal M)}\ \min_{j\in[N]} d_i(S_j)$$
--   be agent $i$'s max-min share, over all allocations into $N$ (possibly empty) bundles. In the greedy round-robin protocol (Algorithm 1) the agents pick in rounds, in the order $1,\dots,N$ in each round, and each picker takes a remaining chore of highest utility for her; ties are broken arbitrarily. The theorem has three parts.
--
--   1. *The protocol always produces an allocation:* for every utility profile there is a round-robin run.
--   2. *The guarantee:* if $d_i(j)\le 0$ for all $i$ and $j$, then for every run, with resulting allocation $(S_1,\dots,S_N)$, and every agent $i$,
--   $$d_i(S_i)\ \ge\ \Big(2-\frac1N\Big)\cdot \mathrm{MmS}^N_{d_i}(\mathcal M).$$
--   3. *The factor cannot be improved:* for every $N\ge1$ and every constant $c<2-\tfrac1N$ there is a chores instance with $N$ agents ($d_i(j)\le 0$ and $d_i\not\equiv 0$ for all $i$) such that every round-robin run leaves some agent $i$ with $d_i(S_i)<c\cdot\mathrm{MmS}^N_{d_i}(\mathcal M)$.
--
--   Since max-min shares of chores are non-positive, part 2 says every agent receives at most $2-\tfrac1N$ times her share of disutility, under every tie-breaking rule, and part 3 says no smaller factor holds for all instances with $N$ agents.
--
--   **Formalization Note** Agents are `Fin N` (the paper's agent $i$ is index $i-1$), chores `Fin m`, utilities `d : Fin N → Fin m → ℝ`, $d_i(S)$ is `bval d i S`, a run is any `σ : Fin m ≃ Fin m` with `IsRoundRobinRun d σ` (pick `t` is made by agent `t % N` and takes a chore that agent weakly prefers to every chore taken at a later pick), $S_i$ is `rrBundle σ i`, and the max-min share is the published `LittleCharity.MMS.mms (bval d i) N univ`. Part 2 needs no assumption that $\mathcal M$ is nonempty: with no chores both sides are $0$.
--
--   Differences from the source:
--   - encoding: "the allocation obtained from Algorithm 1" (the protocol always terminates with an allocation) → part 1, the existence of a run for every profile, stated as a clause; reason: the run is a relation over all tie-breaking rules, and the clause makes explicit that the relation is nonempty, so parts 2 and 3 are not vacuous
--   - generalization: guarantee for chores instances (d_i(j) ≤ 0 and d_i ≢ 0) → guarantee for all non-positive utilities, d_i ≢ 0 dropped; reason: with d_i ≡ 0 both sides are 0, and every chores instance satisfies the Lean hypotheses
--   - reading: "the inequality cannot be improved for general instances" → for every N ≥ 1 and every c < 2 − 1/N there is a chores instance with N agents on which every run leaves some agent below c·MmS; reason: the factor 2 − 1/N depends on N, so the improvement is ruled out for each N separately, and the tie-breaking rule is arbitrary in the protocol, so the instance must defeat every run
-- source:
--   Aziz, Rauchecker, Schryen & Walsh, Algorithms for Max-Min Share Fair Allocation of Indivisible Chores, AAAI 2017, PDF p. 4, Theorem 9 (with Algorithm 1, PDF p. 4; Definitions 1–2, PDF p. 2)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MmSChores_RoundRobin_Setting

namespace MmSChores.RoundRobin

open Finset

/-- Theorem 9 (PDF p. 4). (0) Algorithm 1 always produces an allocation: every utility profile
admits a greedy round-robin run. (a) For every `N ≥ 1` agents with non-positive additive
utilities, every run (every tie-breaking rule) and every agent `i`,
`d_i(S_i) ≥ (2 - 1/N) · MmS^N_{d_i}(M)`. (b) The factor cannot be improved: for every `N ≥ 1`
and every `c < 2 - 1/N` there is a chores instance with `N` agents on which every run leaves
some agent `i` with `d_i(S_i) < c · MmS^N_{d_i}(M)`. -/
theorem theorem_9 :
    (∀ (N m : ℕ) (d : Fin N → Fin m → ℝ), ∃ σ : Fin m ≃ Fin m, IsRoundRobinRun d σ) ∧
    (∀ (N m : ℕ), 0 < N → ∀ d : Fin N → Fin m → ℝ, (∀ i j, d i j ≤ 0) →
      ∀ σ : Fin m ≃ Fin m, IsRoundRobinRun d σ → ∀ i : Fin N,
        (2 - 1 / (N : ℝ)) * LittleCharity.MMS.mms (bval d i) N univ
          ≤ bval d i (rrBundle σ i)) ∧
    (∀ N : ℕ, 0 < N → ∀ c : ℝ, c < 2 - 1 / (N : ℝ) →
      ∃ (m : ℕ) (d : Fin N → Fin m → ℝ), IsChores d ∧
        ∀ σ : Fin m ≃ Fin m, IsRoundRobinRun d σ →
          ∃ i : Fin N, bval d i (rrBundle σ i) < c * LittleCharity.MMS.mms (bval d i) N univ) := by sorry

end MmSChores.RoundRobin
