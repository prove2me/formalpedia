-- Prove2me | Theorems.Thm_KellyKolmogorov_theorem_1_8_kolmogorov_criterion
-- name    : KellyKolmogorov.theorem_1_8_kolmogorov_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:45:52.721675+00:00
-- url     : https://prove2.me/theorems/423ec266-a2ca-496b-b48e-aaaaa80d505a
-- title:
--   Theorem 1.8 — Kolmogorov's criterion for reversibility of a stationary Markov process
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be a stochastic process on a probability space $(\Omega,\mathcal F,\mathbb P)$ taking values in a countable state space $\mathcal S$. Assume the standing assumptions of §1.1: each $X(t)$ is a random variable, $X$ is a Markov process that is time homogeneous and irreducible, and almost every sample path is right-continuous with finitely many jumps in every bounded time interval (it remains in each state for a positive length of time and cannot pass through infinitely many states in finite time). Assume that $X$ is **stationary**, and let $q(j,k)$, $j,k\in\mathcal S$, be its **transition rates**, with $q(j,j)=0$.
--
--   Then $X$ is **reversible** if and only if its transition rates satisfy
--   $$
--   q(j_1,j_2)\,q(j_2,j_3)\cdots q(j_{n-1},j_n)\,q(j_n,j_1)=q(j_1,j_n)\,q(j_n,j_{n-1})\cdots q(j_3,j_2)\,q(j_2,j_1) \tag{1.22}
--   $$
--   for any finite sequence of states $j_1,j_2,\dots,j_n\in\mathcal S$.
--
--   Here reversibility means that for all times $t_1,\dots,t_n$ and every $\tau$ the vectors $(X(t_1),\dots,X(t_n))$ and $(X(\tau-t_1),\dots,X(\tau-t_n))$ have the same distribution. The criterion decides reversibility from the transition rates alone, without computing the equilibrium distribution.
--
--   Differences from the source:
--   - encoding: (X(t1), …, X(tn)) has the same distribution as (Y1, …, Yn) → equality of all cylinder probabilities cylProb μ X t j = μ{X(t_i) = j_i for all i}; reason: the state space is countable, so the law of a random vector in 𝒮ⁿ is fixed by its point masses; same instances
--   - encoding: P(B | A) in the Markov property, 'whenever the conditioning event has positive probability' → ProbabilityTheory.cond μ A B, used only under μ A ≠ 0; reason: Mathlib's conditional measure; the guard is the book's positive-probability proviso
--   - reading: a Markov process is time homogeneous if P(X(t+τ) = k | X(t) = j) does not depend upon t → for every τ > 0, the value is the same at all times t with P(X(t) = j) > 0; reason: the transition probability of a Markov process concerns forward steps and is defined only where the conditioning event has positive probability
--   - reading: irreducible: every state in 𝒮 can be reached from every other state → for j ≠ k there are s and τ > 0 with P(X(s) = j, X(s+τ) = k) > 0; reason: 'k can be reached from j' read as a positive probability of being in j and, a positive time later, in k
--   - reading: remains in each state for a positive length of time and is incapable of passing through an infinite number of states in a finite time → almost every sample path is right-continuous and has finitely many jump points in every bounded interval (HasRegularPaths); reason: right-continuity is the usual convention of Exercise 1.2.1 (p. 9), which the finite-dimensional distributions cannot detect; with it the two clauses are exactly positive holding times and finitely many jumps in finite time
--   - reading: q(j, k) = lim_{τ→0} P(X(t+τ) = k | X(t) = j) / τ for j ≠ k, and q(j, j) = 0 → q is given with IsTransitionRate: q(j, j) = 0 and, for j ≠ k and every t with P(X(t) = j) > 0, the ratio tends to q(j, k) as τ ↓ 0; reason: the transition probability concerns forward steps, so the limit is one-sided; the book presupposes that the limit exists, and tying q to X by this property avoids a default value
--   - encoding: transition rates q(j, k), nonnegative reals → q : 𝒮 → 𝒮 → ℝ≥0; reason: limits of nonnegative ratios are nonnegative; same instances
--   - encoding: any finite sequence of states j1, …, jn ∈ 𝒮 and the closed product q(j1, j2)⋯q(jn, j1) → every j : Fin (n+1) → 𝒮, with finRotate (n+1) as the cyclic successor; reason: Fin (n+1) covers every length n+1 ≥ 1; same instances
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), Theorem 1.8, eq. (1.22), p. 23 (PDF p. 26); standing assumptions §1.1, pp. 1–3 (PDF pp. 4–6); definition of reversibility p. 5 (PDF p. 8)

import Mathlib
import Definitions.Def_KellyKolmogorov_StandingAssumptions
import Definitions.Def_KellyKolmogorov_IsStationary
import Definitions.Def_KellyKolmogorov_IsTransitionRate
import Definitions.Def_KellyKolmogorov_IsReversible
import Definitions.Def_KellyKolmogorov_KolmogorovCycle

open MeasureTheory
open scoped NNReal

namespace KellyKolmogorov

/-- **Theorem 1.8 (Kolmogorov's criterion for a Markov process).**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), Theorem 1.8, p. 23: "A stationary
Markov process is reversible if and only if its transition rates satisfy
`q(j₁, j₂)q(j₂, j₃) ⋯ q(jₙ₋₁, jₙ)q(jₙ, j₁) = q(j₁, jₙ)q(jₙ, jₙ₋₁) ⋯ q(j₃, j₂)q(j₂, j₁)` (1.22)
for any finite sequence of states `j₁, j₂, …, jₙ ∈ 𝒮`."

The process `X(t)`, `t ∈ ℝ`, on the countable state space `𝒮` satisfies the standing
assumptions of §1.1 (Markov, time homogeneous, irreducible, positive holding times, no
explosion), is stationary, and has transition rates `q`. Then `X` is reversible if and only if
`q` satisfies Kolmogorov's cycle condition (1.22). -/
theorem theorem_1_8_kolmogorov_criterion {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮]
    [MeasurableSingletonClass 𝒮] [Countable 𝒮] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → 𝒮) (q : 𝒮 → 𝒮 → ℝ≥0) (hX : StandingAssumptions μ X)
    (hstat : IsStationary μ X) (hq : IsTransitionRate μ X q) :
    IsReversible μ X ↔ KolmogorovCycle q := by sorry

end KellyKolmogorov
