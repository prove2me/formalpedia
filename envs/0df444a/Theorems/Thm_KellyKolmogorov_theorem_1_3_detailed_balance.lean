-- Prove2me | Theorems.Thm_KellyKolmogorov_theorem_1_3_detailed_balance
-- name    : KellyKolmogorov.theorem_1_3_detailed_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:41:15.84428+00:00
-- url     : https://prove2.me/theorems/28419e61-f9c7-45d1-8aa5-6fdeab2cebba
-- title:
--   Theorem 1.3 — detailed balance characterizes reversibility of a stationary Markov process
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be a stochastic process on a probability space $(\Omega,\mathcal F,\mathbb P)$ taking values in a countable state space $\mathcal S$. Assume the standing assumptions of §1.1: each $X(t)$ is a random variable, $X$ is a Markov process that is time homogeneous and irreducible, and almost every sample path is right-continuous with finitely many jumps in every bounded time interval (it remains in each state for a positive length of time and cannot pass through infinitely many states in finite time). Assume that $X$ is **stationary**, and let $q(j,k)$, $j,k\in\mathcal S$, be its **transition rates**, with $q(j,j)=0$.
--
--   Then:
--
--   1. $X$ is **reversible** if and only if there is a collection of positive numbers $\pi(j)$, $j\in\mathcal S$, with $\sum_{j}\pi(j)=1$ that satisfies the **detailed balance conditions**
--   $$
--   \pi(j)\,q(j,k)=\pi(k)\,q(k,j)\qquad j,k\in\mathcal S. \tag{1.6}
--   $$
--   2. When such a collection exists, it is the equilibrium distribution of the process: $\pi(j)=\mathbb P(X(t)=j)$ for every $j\in\mathcal S$ and every time $t$.
--
--   This is the continuous-time analogue of Theorem 1.2 and the step through which Kolmogorov's criterion (Theorem 1.8) is proved.
--
--   **Formalization Note** "Summing to unity" is `HasSum π 1`, which includes summability.
--
--   Differences from the source:
--   - encoding: (X(t1), …, X(tn)) has the same distribution as (Y1, …, Yn) → equality of all cylinder probabilities cylProb μ X t j = μ{X(t_i) = j_i for all i}; reason: the state space is countable, so the law of a random vector in 𝒮ⁿ is fixed by its point masses; same instances
--   - encoding: P(B | A) in the Markov property, 'whenever the conditioning event has positive probability' → ProbabilityTheory.cond μ A B, used only under μ A ≠ 0; reason: Mathlib's conditional measure; the guard is the book's positive-probability proviso
--   - reading: a Markov process is time homogeneous if P(X(t+τ) = k | X(t) = j) does not depend upon t → for every τ > 0, the value is the same at all times t with P(X(t) = j) > 0; reason: the transition probability of a Markov process concerns forward steps and is defined only where the conditioning event has positive probability
--   - reading: irreducible: every state in 𝒮 can be reached from every other state → for j ≠ k there are s and τ > 0 with P(X(s) = j, X(s+τ) = k) > 0; reason: 'k can be reached from j' read as a positive probability of being in j and, a positive time later, in k
--   - reading: remains in each state for a positive length of time and is incapable of passing through an infinite number of states in a finite time → almost every sample path is right-continuous and has finitely many jump points in every bounded interval (HasRegularPaths); reason: right-continuity is the usual convention of Exercise 1.2.1 (p. 9), which the finite-dimensional distributions cannot detect; with it the two clauses are exactly positive holding times and finitely many jumps in finite time
--   - reading: q(j, k) = lim_{τ→0} P(X(t+τ) = k | X(t) = j) / τ for j ≠ k, and q(j, j) = 0 → q is given with IsTransitionRate: q(j, j) = 0 and, for j ≠ k and every t with P(X(t) = j) > 0, the ratio tends to q(j, k) as τ ↓ 0; reason: the transition probability concerns forward steps, so the limit is one-sided; the book presupposes that the limit exists, and tying q to X by this property avoids a default value
--   - encoding: transition rates q(j, k), nonnegative reals → q : 𝒮 → 𝒮 → ℝ≥0; reason: limits of nonnegative ratios are nonnegative; same instances
--   - encoding: positive numbers π(j) summing to unity → ∀ j, 0 < π j and HasSum π 1; reason: HasSum states the convergence explicitly; same instances
--   - reading: it is the equilibrium distribution of the process → π j = P(X(t) = j) for every t and j; reason: the proof (p. 7) takes π(j) = P(X(t) = j); for a stationary process the equilibrium distribution is its one-time distribution
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), Theorem 1.3, pp. 6–7 (PDF pp. 9–10), eq. (1.6); standing assumptions §1.1, pp. 1–3; definition of reversibility p. 5

import Mathlib
import Definitions.Def_KellyKolmogorov_StandingAssumptions
import Definitions.Def_KellyKolmogorov_IsStationary
import Definitions.Def_KellyKolmogorov_IsTransitionRate
import Definitions.Def_KellyKolmogorov_IsReversible
import Definitions.Def_KellyKolmogorov_DetailedBalance

open MeasureTheory
open scoped NNReal

namespace KellyKolmogorov

/-- **Theorem 1.3 (detailed balance characterizes reversibility).**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), Theorem 1.3, pp. 6–7: "A stationary
Markov process is reversible if and only if there exists a collection of positive numbers
`π(j)`, `j ∈ 𝒮`, summing to unity that satisfy the detailed balance conditions
`π(j)q(j, k) = π(k)q(k, j)`, `j, k ∈ 𝒮` (1.6). When there exists such a collection `π(j)`,
`j ∈ 𝒮`, it is the equilibrium distribution of the process."

The process `X` on the countable state space `𝒮` satisfies the standing assumptions of §1.1
(`StandingAssumptions`), is stationary, and has transition rates `q`. Conclusions:
1. `X` is reversible iff some positive `π` with `Σ π = 1` satisfies (1.6);
2. every such `π` is the distribution of `X(t)`, for every `t`. -/
theorem theorem_1_3_detailed_balance {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮]
    [MeasurableSingletonClass 𝒮] [Countable 𝒮] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → 𝒮) (q : 𝒮 → 𝒮 → ℝ≥0) (hX : StandingAssumptions μ X)
    (hstat : IsStationary μ X) (hq : IsTransitionRate μ X q) :
    (IsReversible μ X ↔
        ∃ π : 𝒮 → ℝ, (∀ j, 0 < π j) ∧ HasSum π 1 ∧ DetailedBalance π q) ∧
      ∀ π : 𝒮 → ℝ, (∀ j, 0 < π j) → HasSum π 1 → DetailedBalance π q →
        ∀ (t : ℝ) (j : 𝒮), π j = (μ {ω | X t ω = j}).toReal := by sorry

end KellyKolmogorov
