-- Prove2me | Theorems.Thm_KellyRSN_PartialBalance_partialBalance_iff_boundary
-- name    : KellyRSN.PartialBalance.partialBalance_iff_boundary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:42:12.225499+00:00
-- url     : https://prove2.me/theorems/96de3c50-ad9e-45da-bda2-b060b2e9cca5
-- title:
--   Exercise 1.6.2 (final claim) — partial balance across the boundary of $\mathcal A$
-- statement:
--   Let $q(j,k)$, $j,k \in \mathcal S$, be the transition rates of a Markov process on a countable state space $\mathcal S$ satisfying the standing assumptions of §1.1 ($q(j,j) = 0$, $q(j) = \sum_k q(j,k) < \infty$, irreducible, non-explosive), and let $\pi(j)$, $j \in \mathcal S$, be its equilibrium distribution.
--   Let $\mathcal A \subseteq \mathcal S$. Then $\pi$ satisfies the partial balance conditions (1.24) for $\mathcal A$ if and only if
--   $$
--   \pi(j) \sum_{k \in \mathcal S - \mathcal A} q(j,k) = \sum_{k \in \mathcal S - \mathcal A} \pi(k)\, q(k,j), \qquad j \in \mathcal A .
--   $$
--
--   This boundary form of partial balance says that, at each state of $\mathcal A$, the probability flux to the complement equals the flux from it. It is the form used for the alterations of rates across the boundary and for the exit and entry chains.
--
--   **Formalization Note** Rates, distributions and sums take values in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: a (continuous-time) Markov process with transition rates q(j, k) on a countable state space, under the standing assumptions of §1.1 (time homogeneous, irreducible, positive holding times, non-explosive) → a rate matrix q : S → S → ℝ≥0∞ on a countable S with IsKellyRates q (q(j,j) = 0, q(j) < ∞, irreducible, non-explosive in the form Σ_n 1/q(J_n) = ∞ almost surely along the jump chain); reason: the book never constructs the process from its rates and every statement is about the rates, the equilibrium equations and the jump chain; non-explosion is equivalent to Σ_n 1/q(J_n) = ∞ a.s. (Norris, Markov Chains, Thms 2.3.2 and 2.7.1)
--   - encoding: real rates, probabilities and sums → values and tsums in ℝ≥0∞; reason: an ℝ≥0∞-valued sum is always defined, so no summability side condition can hold vacuously; the instances are the same
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 27 (PDF p. 30), Exercise 1.6.2, final claim ('Observe that ...')

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsKellyRates
import Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
import Definitions.Def_KellyRSN_PartialBalance_IsPartialBalance

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Partial balance across the boundary of `𝒜`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.6.2 (final claim), p. 27
(PDF p. 30): "Observe that the distribution `π(j)`, `j ∈ 𝒮`, satisfies the partial balance
conditions (1.24) if and only if `π(j) Σ_{k∈𝒮−𝒜} q(j, k) = Σ_{k∈𝒮−𝒜} π(k) q(k, j)`, `j ∈ 𝒜`."

For a Markov process satisfying the standing assumptions of §1.1 (`IsKellyRates`) with
equilibrium distribution `π`, and any set `A`, the partial balance conditions (1.24) hold iff the
flux balance across the boundary of `A` holds at every `j ∈ A`.

**Formalization Note.** Rates, distributions and sums are in `ℝ≥0∞`; sums over `𝒮 − 𝒜` are
`tsum`s over the subtype `↥Aᶜ`. -/
theorem partialBalance_iff_boundary
    {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) (hq : IsKellyRates q)
    (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) :
    IsPartialBalance q π A ↔
      ∀ j ∈ A, π j * ∑' k : ↥Aᶜ, q j k = ∑' k : ↥Aᶜ, π k * q k j := by sorry

end KellyRSN.PartialBalance
