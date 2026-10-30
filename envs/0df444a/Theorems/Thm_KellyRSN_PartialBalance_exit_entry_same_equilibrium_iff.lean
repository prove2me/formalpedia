-- Prove2me | Theorems.Thm_KellyRSN_PartialBalance_exit_entry_same_equilibrium_iff
-- name    : KellyRSN.PartialBalance.exit_entry_same_equilibrium_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:46:37.724562+00:00
-- url     : https://prove2.me/theorems/1a89d086-b210-4e83-81d1-d34c218974c4
-- title:
--   Exercise 1.7.8 — exit and entry chains share their equilibrium iff partial balance
-- statement:
--   Let $q(j,k)$, $j,k \in \mathcal S$, be the transition rates of a Markov process on a countable state space $\mathcal S$ satisfying the standing assumptions of §1.1 ($q(j,j) = 0$, $q(j) = \sum_k q(j,k) < \infty$, irreducible, non-explosive), and let $\pi(j)$, $j \in \mathcal S$, be its equilibrium distribution.
--   Let $\mathcal A \subseteq \mathcal S$ with $\mathcal A$ and $\mathcal S - \mathcal A$ non-empty, and suppose that the probability flux out of $\mathcal A$,
--   $$
--   \sum_{j \in \mathcal A} \sum_{k \in \mathcal S - \mathcal A} \pi(j)\, q(j,k),
--   $$
--   is finite. Then the Markov chain formed by observing the process just before it leaves $\mathcal A$ has the same equilibrium distribution as the Markov chain formed by observing the process just after it enters $\mathcal A$ if and only if $\pi$ satisfies the partial balance conditions (1.24) for $\mathcal A$.
--
--   **Formalization Note** The observed chains are read off the jump chain; "the same equilibrium distribution" means each chain has exactly one equilibrium distribution on $\mathcal A$ and the two coincide.
--
--   Differences from the source:
--   - encoding: a (continuous-time) Markov process with transition rates q(j, k) on a countable state space, under the standing assumptions of §1.1 (time homogeneous, irreducible, positive holding times, non-explosive) → a rate matrix q : S → S → ℝ≥0∞ on a countable S with IsKellyRates q (q(j,j) = 0, q(j) < ∞, irreducible, non-explosive in the form Σ_n 1/q(J_n) = ∞ almost surely along the jump chain); reason: the book never constructs the process from its rates and every statement is about the rates, the equilibrium equations and the jump chain; non-explosion is equivalent to Σ_n 1/q(J_n) = ∞ a.s. (Norris, Markov Chains, Thms 2.3.2 and 2.7.1)
--   - encoding: real rates, probabilities and sums → values and tsums in ℝ≥0∞; reason: an ℝ≥0∞-valued sum is always defined, so no summability side condition can hold vacuously; the instances are the same
--   - encoding: a set 𝒜 ⊂ 𝒮 → A : Set S with A.Nonempty; reason: for A = ∅ there is nothing to condition on (π(j)/Σ_{k∈𝒜}π(k) is 0/0) and no process on an empty state space; this only excludes an undefined case
--   - encoding: the Markov chains formed by observing the process just before it leaves 𝒜 and just after it enters 𝒜, and 'has the same equilibrium distribution' → kernels exitKernel q A and entryKernel q A on ↥A read off the jump chain law; SameObservedEquilibrium: each kernel has exactly one stationary probability vector (IsStationaryProb) and the two coincide; vectors vanish on states of A the chain never visits; reason: the process leaves and enters 𝒜 only at jumps, so the observed states are those of the jump chain at its exit and entry steps; 'the' equilibrium distribution follows the book's convention that it is unique when it exists; the chains live on the states with a positive rate out of (into) 𝒜 and their distributions are extended by 0 to the rest of A
--   - encoding: (vi) for a set 𝒜 ⊂ 𝒮 → additional hypothesis (Aᶜ).Nonempty; reason: for A = S the process never leaves or enters A and the two observed chains do not exist; this only excludes an undefined case
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 33 (PDF p. 36), Exercise 1.7.8

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsKellyRates
import Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
import Definitions.Def_KellyRSN_PartialBalance_IsPartialBalance
import Definitions.Def_KellyRSN_PartialBalance_fluxOut
import Definitions.Def_KellyRSN_PartialBalance_SameObservedEquilibrium

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Exit and entry chains of `𝒜` share their equilibrium iff partial balance holds.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.7.8, p. 33 (PDF p. 36):
"Consider a Markov process with transition rates `q(j, k)`, `j, k ∈ 𝒮`, and equilibrium
distribution `π(j)`, `j ∈ 𝒮`. Suppose that the probability flux out of the set `𝒜`
`Σ_{j∈𝒜} Σ_{k∈𝒮−𝒜} π(j) q(j, k)` is finite. Show that the Markov chain formed by observing the
process at those instants in time just before it leaves the set `𝒜` has the same equilibrium
distribution as the Markov chain formed by observing the process at those instants in time just
after it enters the set `𝒜` if and only if the partial balance conditions (1.24) are satisfied."

**Formalization Note.** The two observed chains are read off the jump chain (`exitKernel`,
`entryKernel`); "has the same equilibrium distribution" is `SameObservedEquilibrium` (each chain
has exactly one equilibrium distribution and they coincide). `A` and `𝒮 − 𝒜` are non-empty:
otherwise the process never leaves or never enters `A` and the two chains do not exist. -/
theorem exit_entry_same_equilibrium_iff
    {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) (hq : IsKellyRates q)
    (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) (hAc : (Aᶜ).Nonempty) (hflux : fluxOut q π A ≠ ⊤) :
    SameObservedEquilibrium q A ↔ IsPartialBalance q π A := by sorry

end KellyRSN.PartialBalance
