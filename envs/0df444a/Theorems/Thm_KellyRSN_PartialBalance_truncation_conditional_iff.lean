-- Prove2me | Theorems.Thm_KellyRSN_PartialBalance_truncation_conditional_iff
-- name    : KellyRSN.PartialBalance.truncation_conditional_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:43:27.574695+00:00
-- url     : https://prove2.me/theorems/630c1b1f-c275-4d99-b6d1-5b42428d6315
-- title:
--   Exercise 1.6.2 — truncation yields the conditional distribution iff partial balance
-- statement:
--   Let $q(j,k)$, $j,k \in \mathcal S$, be the transition rates of a Markov process on a countable state space $\mathcal S$ satisfying the standing assumptions of §1.1 ($q(j,j) = 0$, $q(j) = \sum_k q(j,k) < \infty$, irreducible, non-explosive), and let $\pi(j)$, $j \in \mathcal S$, be its equilibrium distribution.
--   Let $\mathcal A \subseteq \mathcal S$ be non-empty. Then the conditional distribution
--   $$
--   \frac{\pi(j)}{\sum_{k \in \mathcal A} \pi(k)}, \qquad j \in \mathcal A,
--   $$
--   is an equilibrium distribution of the process truncated to $\mathcal A$ (rates $q(j,k)$, $j,k \in \mathcal A$) if and only if $\pi$ satisfies the partial balance conditions (1.24) for $\mathcal A$.
--
--   **Formalization Note** The truncated process is the rate matrix on $\mathcal A$; it is not assumed irreducible.
--
--   Differences from the source:
--   - encoding: a (continuous-time) Markov process with transition rates q(j, k) on a countable state space, under the standing assumptions of §1.1 (time homogeneous, irreducible, positive holding times, non-explosive) → a rate matrix q : S → S → ℝ≥0∞ on a countable S with IsKellyRates q (q(j,j) = 0, q(j) < ∞, irreducible, non-explosive in the form Σ_n 1/q(J_n) = ∞ almost surely along the jump chain); reason: the book never constructs the process from its rates and every statement is about the rates, the equilibrium equations and the jump chain; non-explosion is equivalent to Σ_n 1/q(J_n) = ∞ a.s. (Norris, Markov Chains, Thms 2.3.2 and 2.7.1)
--   - encoding: real rates, probabilities and sums → values and tsums in ℝ≥0∞; reason: an ℝ≥0∞-valued sum is always defined, so no summability side condition can hold vacuously; the instances are the same
--   - encoding: a set 𝒜 ⊂ 𝒮 → A : Set S with A.Nonempty; reason: for A = ∅ there is nothing to condition on (π(j)/Σ_{k∈𝒜}π(k) is 0/0) and no process on an empty state space; this only excludes an undefined case
--   - reading: the equilibrium distribution of the truncated process is the conditional distribution → condDist π A is an equilibrium distribution (IsEquilibriumDist) of truncRates q A; reason: the book defines an equilibrium distribution as a positive solution of (1.3) summing to one and states it is unique when it exists (p. 3); the Lean does not assume the truncated process non-explosive, and for an irreducible truncation 'is an' and 'is the' coincide
--   - generalization: truncation to 𝒜 requires the resulting process to be irreducible within the state space 𝒜 (p. 25) → no irreducibility assumption on the truncated rates truncRates q A; reason: the equivalence holds for every A; restricted to the A for which the truncated process is irreducible it is exactly the book's statement
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 27 (PDF p. 30), Exercise 1.6.2

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsKellyRates
import Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
import Definitions.Def_KellyRSN_PartialBalance_IsPartialBalance
import Definitions.Def_KellyRSN_PartialBalance_truncRates
import Definitions.Def_KellyRSN_PartialBalance_condDist

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Truncation to `𝒜` yields the conditional distribution iff partial balance holds.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.6.2, p. 27 (PDF p. 30):
"Suppose that a Markov process with equilibrium distribution `π(j)`, `j ∈ 𝒮`, is truncated to the
set `𝒜 ⊂ 𝒮`. Show that the equilibrium distribution of the truncated process is the conditional
probability distribution `π(j) / Σ_{k∈𝒜} π(k)`, `j ∈ 𝒜` if and only if the distribution `π(j)`,
`j ∈ 𝒮`, satisfies `π(j) Σ_{k∈𝒜} q(j, k) = Σ_{k∈𝒜} π(k) q(k, j)`, `j ∈ 𝒜` (1.24)."

**Formalization Note.** "The equilibrium distribution of the truncated process is `ρ`" is stated as
"`ρ` is an equilibrium distribution of the truncated rates `truncRates q A`" (positive, summing to
one, solving (1.3) on `A`); when the truncated process is irreducible (the book's truncation
requirement, p. 25) it has at most one. That irreducibility requirement is not assumed: the
equivalence holds without it. `A` is non-empty (otherwise the conditional distribution is
undefined). -/
theorem truncation_conditional_iff
    {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) (hq : IsKellyRates q)
    (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) :
    IsEquilibriumDist (truncRates q A) (condDist π A) ↔ IsPartialBalance q π A := by sorry

end KellyRSN.PartialBalance
