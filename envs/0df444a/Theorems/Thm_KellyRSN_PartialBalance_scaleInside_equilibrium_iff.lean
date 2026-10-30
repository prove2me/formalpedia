-- Prove2me | Theorems.Thm_KellyRSN_PartialBalance_scaleInside_equilibrium_iff
-- name    : KellyRSN.PartialBalance.scaleInside_equilibrium_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:44:15.908781+00:00
-- url     : https://prove2.me/theorems/dfd67cc3-2ec4-4783-b370-747bf0eac72f
-- title:
--   Exercise 1.6.3 — scaling rates inside $\mathcal A$ keeps $\pi$ iff partial balance
-- statement:
--   Let $q(j,k)$, $j,k \in \mathcal S$, be the transition rates of a Markov process on a countable state space $\mathcal S$ satisfying the standing assumptions of §1.1 ($q(j,j) = 0$, $q(j) = \sum_k q(j,k) < \infty$, irreducible, non-explosive), and let $\pi(j)$, $j \in \mathcal S$, be its equilibrium distribution.
--   Let $\mathcal A \subseteq \mathcal S$ and let $c$ be a real number with $c > 0$ and $c \ne 1$. Alter the process by changing $q(j,k)$ to $c\,q(j,k)$ for $j, k \in \mathcal A$. Then $\pi$ is an equilibrium distribution of the altered process if and only if $\pi$ satisfies the partial balance conditions (1.24) for $\mathcal A$.
--
--   **Formalization Note** $c$ is a non-negative real number with $c \ne 0$, $c \ne 1$.
--
--   Differences from the source:
--   - encoding: a (continuous-time) Markov process with transition rates q(j, k) on a countable state space, under the standing assumptions of §1.1 (time homogeneous, irreducible, positive holding times, non-explosive) → a rate matrix q : S → S → ℝ≥0∞ on a countable S with IsKellyRates q (q(j,j) = 0, q(j) < ∞, irreducible, non-explosive in the form Σ_n 1/q(J_n) = ∞ almost surely along the jump chain); reason: the book never constructs the process from its rates and every statement is about the rates, the equilibrium equations and the jump chain; non-explosion is equivalent to Σ_n 1/q(J_n) = ∞ a.s. (Norris, Markov Chains, Thms 2.3.2 and 2.7.1)
--   - encoding: real rates, probabilities and sums → values and tsums in ℝ≥0∞; reason: an ℝ≥0∞-valued sum is always defined, so no summability side condition can hold vacuously; the instances are the same
--   - encoding: c ≠ 0 or 1 → c : ℝ≥0 with c ≠ 0 and c ≠ 1, the equivalence asserted for each such c; reason: rates are non-negative real numbers, so only c > 0 gives a Markov process; the book's statement is for an arbitrary such c
--   - reading: the resulting process has the same (unaltered) equilibrium distribution π → π is an equilibrium distribution (IsEquilibriumDist) of scaleInside q A c; reason: an equilibrium distribution is unique when it exists (p. 3); the Lean does not assume the altered process non-explosive, so it states the equilibrium equations, positivity and normalization directly
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 27 (PDF p. 30), Exercise 1.6.3

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsKellyRates
import Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
import Definitions.Def_KellyRSN_PartialBalance_IsPartialBalance
import Definitions.Def_KellyRSN_PartialBalance_scaleInside

open scoped ENNReal NNReal

namespace KellyRSN.PartialBalance

/-- **Scaling the rates inside `𝒜` keeps `π` iff partial balance holds.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.6.3, p. 27 (PDF p. 30):
"Suppose that a Markov process with equilibrium distribution `π(j)`, `j ∈ 𝒮`, is altered by
changing the transition rate `q(j, k)` to `c q(j, k)` for `j, k ∈ 𝒜`, where `c ≠ 0` or `1`. Show
that the resulting Markov process has the same equilibrium distribution if and only if the partial
balance conditions (1.24) are satisfied."

**Formalization Note.** `c : ℝ≥0` with `c ≠ 0`, `c ≠ 1`; the equivalence is asserted for each such
`c`. "Has the same equilibrium distribution" is stated as "`π` is an equilibrium distribution of
the altered rates `scaleInside q A c`". -/
theorem scaleInside_equilibrium_iff
    {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) (hq : IsKellyRates q)
    (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (c : ℝ≥0) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    IsEquilibriumDist (scaleInside q A c) π ↔ IsPartialBalance q π A := by sorry

end KellyRSN.PartialBalance
