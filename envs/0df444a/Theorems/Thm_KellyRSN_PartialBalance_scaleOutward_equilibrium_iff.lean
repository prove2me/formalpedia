-- Prove2me | Theorems.Thm_KellyRSN_PartialBalance_scaleOutward_equilibrium_iff
-- name    : KellyRSN.PartialBalance.scaleOutward_equilibrium_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:44:55.085833+00:00
-- url     : https://prove2.me/theorems/a59d9f9d-5e43-4ff4-9a27-935d019135e4
-- title:
--   Exercise 1.6.4 — scaling rates out of $\mathcal A$ gives $B\pi$ / $Bc\pi$ iff partial balance
-- statement:
--   Let $q(j,k)$, $j,k \in \mathcal S$, be the transition rates of a Markov process on a countable state space $\mathcal S$ satisfying the standing assumptions of §1.1 ($q(j,j) = 0$, $q(j) = \sum_k q(j,k) < \infty$, irreducible, non-explosive), and let $\pi(j)$, $j \in \mathcal S$, be its equilibrium distribution.
--   Let $\mathcal A \subseteq \mathcal S$ and let $c$ be a real number with $c > 0$ and $c \ne 1$. Alter the process by changing $q(j,k)$ to $c\,q(j,k)$ for $j \in \mathcal A$, $k \in \mathcal S - \mathcal A$. Then the altered process has an equilibrium distribution of the form
--   $$
--   B\pi(j), \quad j \in \mathcal A, \qquad\qquad Bc\,\pi(j), \quad j \in \mathcal S - \mathcal A,
--   $$
--   for some constant $B$, if and only if $\pi$ satisfies the partial balance conditions (1.24) for $\mathcal A$. The normalization forces $B^{-1} = \sum_{j \in \mathcal A} \pi(j) + c \sum_{j \in \mathcal S - \mathcal A} \pi(j)$.
--
--   **Formalization Note** $c$ is a non-negative real number with $c \ne 0$, $c \ne 1$; $B \in [0,\infty]$ is existentially quantified.
--
--   Differences from the source:
--   - encoding: a (continuous-time) Markov process with transition rates q(j, k) on a countable state space, under the standing assumptions of §1.1 (time homogeneous, irreducible, positive holding times, non-explosive) → a rate matrix q : S → S → ℝ≥0∞ on a countable S with IsKellyRates q (q(j,j) = 0, q(j) < ∞, irreducible, non-explosive in the form Σ_n 1/q(J_n) = ∞ almost surely along the jump chain); reason: the book never constructs the process from its rates and every statement is about the rates, the equilibrium equations and the jump chain; non-explosion is equivalent to Σ_n 1/q(J_n) = ∞ a.s. (Norris, Markov Chains, Thms 2.3.2 and 2.7.1)
--   - encoding: real rates, probabilities and sums → values and tsums in ℝ≥0∞; reason: an ℝ≥0∞-valued sum is always defined, so no summability side condition can hold vacuously; the instances are the same
--   - encoding: c ≠ 0 or 1 → c : ℝ≥0 with c ≠ 0 and c ≠ 1, the equivalence asserted for each such c; reason: rates are non-negative real numbers, so only c > 0 gives a Markov process; the book's statement is for an arbitrary such c
--   - encoding: Bπ(j), j ∈ 𝒜; Bcπ(j), j ∈ 𝒮 − 𝒜, with B a normalizing constant → ∃ B : ℝ≥0∞ such that (j ↦ if j ∈ A then B π j else B c π j) is an equilibrium distribution; reason: summing to one forces B⁻¹ = Σ_{j∈𝒜} π(j) + c Σ_{j∈𝒮−𝒜} π(j) (Lemma 1.9's constant, p. 25), so the existential loses nothing
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 27 (PDF p. 30), Exercise 1.6.4 (normalizing constant: p. 25, PDF p. 28, proof of Lemma 1.9)

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsKellyRates
import Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
import Definitions.Def_KellyRSN_PartialBalance_IsPartialBalance
import Definitions.Def_KellyRSN_PartialBalance_scaleOutward

open scoped ENNReal NNReal

namespace KellyRSN.PartialBalance

open Classical in
/-- **Scaling the rates out of `𝒜` gives `Bπ` on `𝒜`, `Bcπ` off `𝒜` iff partial balance holds.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.6.4, p. 27 (PDF p. 30):
"Suppose that a Markov process with equilibrium distribution `π(j)`, `j ∈ 𝒮`, is altered by
changing the transition rate `q(j, k)` to `c q(j, k)` for `j ∈ 𝒜`, `k ∈ 𝒮 − 𝒜`, where `c ≠ 0` or
`1`. Show that the resulting Markov process has an equilibrium distribution of the form
`Bπ(j)`, `j ∈ 𝒜`; `Bcπ(j)`, `j ∈ 𝒮 − 𝒜` if and only if the distribution `π(j)`, `j ∈ 𝒮`,
satisfies the partial balance conditions (1.24)."

**Formalization Note.** `c : ℝ≥0` with `c ≠ 0`, `c ≠ 1`, for each such `c`. The constant `B` is
existentially quantified in `ℝ≥0∞`; normalization forces
`B⁻¹ = Σ_{j∈𝒜} π(j) + c Σ_{j∈𝒮−𝒜} π(j)` (the constant of Lemma 1.9, p. 25, PDF p. 28). -/
theorem scaleOutward_equilibrium_iff
    {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) (hq : IsKellyRates q)
    (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (c : ℝ≥0) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (∃ B : ℝ≥0∞, IsEquilibriumDist (scaleOutward q A c)
        (fun j => if j ∈ A then B * π j else B * (c : ℝ≥0∞) * π j)) ↔
      IsPartialBalance q π A := by sorry

end KellyRSN.PartialBalance
