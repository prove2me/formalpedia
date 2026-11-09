-- Prove2me | Theorems.Thm_GeneralizedUniformServer_UnitWeights_configuration_law
-- name    : GeneralizedUniformServer.UnitWeights.configuration_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:33.580091+00:00
-- url     : https://prove2.me/theorems/646721d0-6cf5-4b6d-8fa2-1ed92191a53e
-- title:
--   Lemma 3.1 — the algorithm's configuration $X_t$ has law $\mu_t$
-- statement:
--   Let $k\ge1$, let $a$ be the initial configuration and fix a finite request sequence $\rho=(r_1,\dots,r_T)$. Let $X_0=a,X_1,\dots,X_T$ be the configurations of the algorithm of §3.2. For every $0\le t\le T$ and every configuration $y$,
--   $$\Pr[X_t=y]=\mu_t(y)=\frac{\phi_t(y)}{\Phi_t}.$$
--
--   This is the invariant that ties the randomized algorithm to the deterministic weights; Lemma 3.2 uses it to compute the probability that the algorithm moves.
--
--   **Formalization Note** The probability is computed from the joint trajectory law, and the right-hand side is a quotient in $[0,\infty]$ of the weights after the prefix $(r_1,\dots,r_t)$.
--
--   Differences from the source:
--   - encoding: configurations on pairwise disjoint spaces, finite request sequences and unit movement costs → dependent configurations indexed by `Fin k`, request lists with 0-based entries, finite schedules where used, and natural-valued Hamming costs and OPT; reason: tagged coordinates preserve each space, the list and schedule indices relabel the source times, and every unit-weight cost is a natural number, with OPT attained over the nonempty feasible set
--   - encoding: every $t\ge0$ of a request sequence → every $0\le t\le T$ of a finite list of requests, with $\Pr[X_t=y]$ read off the reversed trajectory law and the quotient taken in $[0,\infty]$; reason: these are exactly the times at which $X_t$ is defined for a finite sequence, and every prefix of an infinite sequence is such a list
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 9, Lemma 3.1

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Algorithm

open scoped NNReal

namespace GeneralizedUniformServer.UnitWeights

/-- Lemma 3.1 (source p. 9): for every fixed request sequence and every `t ≥ 0`, the
configuration `X_t` of the algorithm has distribution `μ_t = ϕ_t / Φ_t`. Here `X_t` is the
head of the reversed trajectory, and `t` ranges over the times `0 ≤ t ≤ T` of the finite
sequence `ρ = (r₁, …, r_T)`. -/
theorem configuration_law {k : ℕ} [NeZero k] {M : Fin k → Type*}
    (a : Config M) (ρ : List (Config M)) (t : ℕ) (ht : t ≤ ρ.length) (y : Config M) :
    ((algTraj a ρ t).map fun p => p.headD a) y =
      ((weights a (ρ.take t) y : ℝ≥0) : ENNReal) / ((totalWeight a (ρ.take t) : ℝ≥0) : ENNReal) := by sorry

end GeneralizedUniformServer.UnitWeights
