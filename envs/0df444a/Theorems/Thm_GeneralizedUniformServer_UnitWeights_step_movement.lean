-- Prove2me | Theorems.Thm_GeneralizedUniformServer_UnitWeights_step_movement
-- name    : GeneralizedUniformServer.UnitWeights.step_movement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:29.463724+00:00
-- url     : https://prove2.me/theorems/cb35d3dc-9f02-4712-96b9-ad3e7deb4f4b
-- title:
--   Lemma 3.2 — one-step movement $\mathbb E[d(X_{t-1},X_t)]\le(k+1)\ln(\Phi_{t-1}/\Phi_t)$
-- statement:
--   Let $k\ge1$, let $a$ be the initial configuration and fix a finite request sequence $\rho=(r_1,\dots,r_T)$. For the algorithm of §3.2 and every $1\le t\le T$,
--   $$\mathbb E\bigl[d(X_{t-1},X_t)\bigr]\le(k+1)\ln\frac{\Phi_{t-1}}{\Phi_t}.$$
--
--   Summing over $t$ and using $\Phi_0=1$ bounds the algorithm's expected cost by $(k+1)\ln(1/\Phi_T)$, the first half of the proof of Theorem 1.1.
--
--   **Formalization Note** The expectation is over the joint law of the trajectory up to time $t$ (its two last entries are $X_{t-1},X_t$), computed in $[0,\infty]$; the right-hand side is embedded with `ENNReal.ofReal`, which is faithful because $\Phi_t\le\Phi_{t-1}$ makes the logarithm nonnegative.
--
--   Differences from the source:
--   - encoding: configurations on pairwise disjoint spaces, finite request sequences and unit movement costs → dependent configurations indexed by `Fin k`, request lists with 0-based entries, finite schedules where used, and natural-valued Hamming costs and OPT; reason: tagged coordinates preserve each space, the list and schedule indices relabel the source times, and every unit-weight cost is a natural number, with OPT attained over the nonempty feasible set
--   - encoding: $\mathbb E[d(X_{t-1},X_t)]$ in $\mathbb R$ for $t\ge1$ → an expectation in $[0,\infty]$ bounded by `ENNReal.ofReal` of the real right-hand side, for $1\le t\le T$ of a finite list of requests; reason: the expectation is finite (at most $k$) and the right-hand side is nonnegative, so the two inequalities are equivalent, and these are the times at which $X_t$ is defined
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 9, Lemma 3.2

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Algorithm

namespace GeneralizedUniformServer.UnitWeights

/-- Lemma 3.2 (source p. 9): for every fixed request sequence and every `t ≥ 1`,
`E[d(X_{t-1}, X_t)] ≤ (k + 1) ln(Φ_{t-1} / Φ_t)`. The expectation is taken under the joint
law of the trajectory up to time `t` (its two most recent entries are `X_t`, `X_{t-1}`),
computed in `ℝ≥0∞`; `t` ranges over `1 ≤ t ≤ T` for the finite sequence `ρ`. -/
theorem step_movement {k : ℕ} [NeZero k] {M : Fin k → Type*}
    (a : Config M) (ρ : List (Config M)) (t : ℕ) (ht₁ : 1 ≤ t) (ht : t ≤ ρ.length) :
    ∑' p : List (Config M), algTraj a ρ t p * (lastStepCost p : ENNReal) ≤
      ENNReal.ofReal (((k : ℝ) + 1) *
        Real.log ((totalWeight a (ρ.take (t - 1)) : ℝ) / (totalWeight a (ρ.take t) : ℝ))) := by sorry

end GeneralizedUniformServer.UnitWeights
