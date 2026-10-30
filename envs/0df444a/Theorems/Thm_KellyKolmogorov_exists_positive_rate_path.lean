-- Prove2me | Theorems.Thm_KellyKolmogorov_exists_positive_rate_path
-- name    : KellyKolmogorov.exists_positive_rate_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:42:43.948992+00:00
-- url     : https://prove2.me/theorems/37c55330-01eb-4835-8764-30e540c2ea4e
-- title:
--   Proof of Theorem 1.7 (rate analogue) — irreducibility gives a path of positive rates
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be a stochastic process on a probability space $(\Omega,\mathcal F,\mathbb P)$ taking values in a countable state space $\mathcal S$. Assume the standing assumptions of §1.1: each $X(t)$ is a random variable, $X$ is a Markov process that is time homogeneous and irreducible, and almost every sample path is right-continuous with finitely many jumps in every bounded time interval (it remains in each state for a positive length of time and cannot pass through infinitely many states in finite time). Assume that $X$ is **stationary**, and let $q(j,k)$, $j,k\in\mathcal S$, be its **transition rates**, with $q(j,j)=0$.
--
--   Then for any two states $j,j_0\in\mathcal S$ there is a finite sequence of states $j=a_0,a_1,\dots,a_m=j_0$ leading from $j$ to $j_0$ with
--   $$
--   q(a_0,a_1)\,q(a_1,a_2)\cdots q(a_{m-1},a_m)>0 .
--   $$
--
--   This turns irreducibility of the process, a property of its transition probabilities, into a property of its transition rates, which is what the construction of the potential in Kolmogorov's criterion needs. For $j=j_0$ the one-element sequence is allowed.
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
--   - encoding: a sequence of states j, jn, …, j1, j0 leading from j to j0 and the products p(j, jn)⋯p(j1, j0), p(j0, j1)⋯p(jn, j) → a list l with IsPathFromTo l j j₀, fwdProd w l and revProd w l; reason: lists of states with first and last element fixed; same instances
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), proof of Theorem 1.7, p. 22 (PDF p. 25), second paragraph; carried over to Markov processes, p. 23 (PDF p. 26)

import Mathlib
import Definitions.Def_KellyKolmogorov_StandingAssumptions
import Definitions.Def_KellyKolmogorov_IsStationary
import Definitions.Def_KellyKolmogorov_IsTransitionRate
import Definitions.Def_KellyKolmogorov_fwdProd
import Definitions.Def_KellyKolmogorov_IsPathFromTo

open MeasureTheory
open scoped NNReal

namespace KellyKolmogorov

/-- **Irreducibility gives a path of positive rates between any two states.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), proof of Theorem 1.7, p. 22 (carried
over to Markov processes on p. 23): "Since the process is irreducible, for any state `j ∈ 𝒮` there
exists a sequence of states `j, jₙ, jₙ₋₁, …, j₁, j₀` leading from `j` to `j₀` such that
`p(j, jₙ)p(jₙ, jₙ₋₁) ⋯ p(j₁, j₀) > 0`."

For a stationary process `X` satisfying the standing assumptions of §1.1 with transition rates
`q`: for all states `j, j₀` there is a sequence of states from `j` to `j₀` along which the
product of the transition rates is positive. -/
theorem exists_positive_rate_path {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮]
    [MeasurableSingletonClass 𝒮] [Countable 𝒮] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → 𝒮) (q : 𝒮 → 𝒮 → ℝ≥0) (hX : StandingAssumptions μ X)
    (hstat : IsStationary μ X) (hq : IsTransitionRate μ X q) :
    ∀ j j₀ : 𝒮, ∃ l : List 𝒮, IsPathFromTo l j j₀ ∧ 0 < fwdProd q l := by sorry

end KellyKolmogorov
