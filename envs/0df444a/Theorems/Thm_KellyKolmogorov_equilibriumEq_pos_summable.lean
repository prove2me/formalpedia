-- Prove2me | Theorems.Thm_KellyKolmogorov_equilibriumEq_pos_summable
-- name    : KellyKolmogorov.equilibriumEq_pos_summable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:44:51.395234+00:00
-- url     : https://prove2.me/theorems/9d769ce7-2355-4d00-9a70-1118343d1263
-- title:
--   Proof of Theorem 1.7 (rate analogue) — positive solutions of (1.3) of a stationary process have finite sum
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be a stochastic process on a probability space $(\Omega,\mathcal F,\mathbb P)$ taking values in a countable state space $\mathcal S$. Assume the standing assumptions of §1.1: each $X(t)$ is a random variable, $X$ is a Markov process that is time homogeneous and irreducible, and almost every sample path is right-continuous with finitely many jumps in every bounded time interval (it remains in each state for a positive length of time and cannot pass through infinitely many states in finite time). Assume that $X$ is **stationary**, and let $q(j,k)$, $j,k\in\mathcal S$, be its **transition rates**, with $q(j,j)=0$.
--
--   Then every collection of positive numbers $m(j)$, $j\in\mathcal S$, satisfying the equilibrium equations
--   $$
--   m(j)\sum_{k\in\mathcal S}q(j,k)=\sum_{k\in\mathcal S}m(k)\,q(k,j)\qquad j\in\mathcal S \tag{1.3}
--   $$
--   has a finite sum $\sum_j m(j)<\infty$.
--
--   In the proof of Kolmogorov's criterion this lets the potential be normalized to an equilibrium distribution ("hence $B$ can be chosen so they sum to unity").
--
--   Differences from the source:
--   - encoding: (X(t1), …, X(tn)) has the same distribution as (Y1, …, Yn) → equality of all cylinder probabilities cylProb μ X t j = μ{X(t_i) = j_i for all i}; reason: the state space is countable, so the law of a random vector in 𝒮ⁿ is fixed by its point masses; same instances
--   - encoding: P(B | A) in the Markov property, 'whenever the conditioning event has positive probability' → ProbabilityTheory.cond μ A B, used only under μ A ≠ 0; reason: Mathlib's conditional measure; the guard is the book's positive-probability proviso
--   - reading: a Markov process is time homogeneous if P(X(t+τ) = k | X(t) = j) does not depend upon t → for every τ > 0, the value is the same at all times t with P(X(t) = j) > 0; reason: the transition probability of a Markov process concerns forward steps and is defined only where the conditioning event has positive probability
--   - reading: irreducible: every state in 𝒮 can be reached from every other state → for j ≠ k there are s and τ > 0 with P(X(s) = j, X(s+τ) = k) > 0; reason: 'k can be reached from j' read as a positive probability of being in j and, a positive time later, in k
--   - reading: remains in each state for a positive length of time and is incapable of passing through an infinite number of states in a finite time → almost every sample path is right-continuous and has finitely many jump points in every bounded interval (HasRegularPaths); reason: right-continuity is the usual convention of Exercise 1.2.1 (p. 9), which the finite-dimensional distributions cannot detect; with it the two clauses are exactly positive holding times and finitely many jumps in finite time
--   - reading: q(j, k) = lim_{τ→0} P(X(t+τ) = k | X(t) = j) / τ for j ≠ k, and q(j, j) = 0 → q is given with IsTransitionRate: q(j, j) = 0 and, for j ≠ k and every t with P(X(t) = j) > 0, the ratio tends to q(j, k) as τ ↓ 0; reason: the transition probability concerns forward steps, so the limit is one-sided; the book presupposes that the limit exists, and tying q to X by this property avoids a default value
--   - encoding: transition rates q(j, k), nonnegative reals → q : 𝒮 → 𝒮 → ℝ≥0; reason: limits of nonnegative ratios are nonnegative; same instances
--   - reading: the step is written for a Markov chain with transition probabilities p → stated for the Markov process X with transition rates q; reason: p. 23: 'The proof of Theorem 1.7 has a direct analogue for a Markov process which establishes the next result'
--   - generalization: 'they' — the potential π(j) built in the proof — cannot sum to infinity → every family of positive numbers solving (1.3) for q is summable; reason: the potential is such a family (it is positive and solves (1.3)), so the Lean statement specializes to the book's; p. 3 states the same principle
--   - encoding: cannot sum to infinity → Summable m; reason: m is positive, so summability is a finite sum
--   - encoding: the sums in (1.3) → computed in ℝ≥0∞ (EquilibriumEq); reason: every term is nonnegative; a real tsum would make (1.3) hold vacuously for divergent series
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), proof of Theorem 1.7, p. 22 (PDF p. 25); carried over to Markov processes, p. 23 (PDF p. 26); compare §1.1, p. 3 (PDF p. 6)

import Mathlib
import Definitions.Def_KellyKolmogorov_StandingAssumptions
import Definitions.Def_KellyKolmogorov_IsStationary
import Definitions.Def_KellyKolmogorov_IsTransitionRate
import Definitions.Def_KellyKolmogorov_EquilibriumEq

open MeasureTheory
open scoped NNReal

namespace KellyKolmogorov

/-- **A stationary process admits no positive solution of (1.3) with infinite sum.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), proof of Theorem 1.7, p. 22 (carried
over to Markov processes on p. 23): "Since the process is stationary they cannot sum to infinity;
hence `B` can be chosen so they sum to unity." Compare §1.1, p. 3: "An equilibrium distribution
will not exist if we can find a collection of positive numbers satisfying equations (1.3) whose
sum is infinite."

For a stationary process `X` satisfying the standing assumptions of §1.1 with transition rates
`q`, every family of positive numbers `m(j)` satisfying the equilibrium equations (1.3) has a
finite sum. -/
theorem equilibriumEq_pos_summable {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮]
    [MeasurableSingletonClass 𝒮] [Countable 𝒮] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → 𝒮) (q : 𝒮 → 𝒮 → ℝ≥0) (hX : StandingAssumptions μ X)
    (hstat : IsStationary μ X) (hq : IsTransitionRate μ X q) :
    ∀ m : 𝒮 → ℝ, (∀ j, 0 < m j) → EquilibriumEq m q → Summable m := by sorry

end KellyKolmogorov
