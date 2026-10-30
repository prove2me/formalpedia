-- Prove2me | Theorems.Thm_KellyRSN_PartialBalance_reversal_truncation_commute_iff
-- name    : KellyRSN.PartialBalance.reversal_truncation_commute_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:45:42.896574+00:00
-- url     : https://prove2.me/theorems/aa258998-abc3-4424-9f64-c1f252c5de72
-- title:
--   Exercise 1.7.7 — time reversal and truncation commute iff partial balance
-- statement:
--   Let $q(j,k)$, $j,k \in \mathcal S$, be the transition rates of a Markov process on a countable state space $\mathcal S$ satisfying the standing assumptions of §1.1 ($q(j,j) = 0$, $q(j) = \sum_k q(j,k) < \infty$, irreducible, non-explosive), and let $\pi(j)$, $j \in \mathcal S$, be its equilibrium distribution.
--   Let $\mathcal A \subseteq \mathcal S$ be non-empty. Let $Y(t)$ be the stationary process truncated to $\mathcal A$ and $Z(t)$ the stationary process obtained by truncating the reversed process $X(-t)$ to $\mathcal A$. Then $Z(t)$ and $Y(-t)$ have the same transition rates — the operations of time reversal and truncation to $\mathcal A$ commute — if and only if $\pi$ satisfies the partial balance conditions (1.24) for $\mathcal A$.
--
--   **Formalization Note** "Commute" means: for some equilibrium distribution $\mu$ of the truncated rates, $\mu(k)q(k,j)/\mu(j) = \pi(k)q(k,j)/\pi(j)$ for all $j,k \in \mathcal A$ (rates of reversed processes by Theorem 1.12).
--
--   Differences from the source:
--   - encoding: a (continuous-time) Markov process with transition rates q(j, k) on a countable state space, under the standing assumptions of §1.1 (time homogeneous, irreducible, positive holding times, non-explosive) → a rate matrix q : S → S → ℝ≥0∞ on a countable S with IsKellyRates q (q(j,j) = 0, q(j) < ∞, irreducible, non-explosive in the form Σ_n 1/q(J_n) = ∞ almost surely along the jump chain); reason: the book never constructs the process from its rates and every statement is about the rates, the equilibrium equations and the jump chain; non-explosion is equivalent to Σ_n 1/q(J_n) = ∞ a.s. (Norris, Markov Chains, Thms 2.3.2 and 2.7.1)
--   - encoding: real rates, probabilities and sums → values and tsums in ℝ≥0∞; reason: an ℝ≥0∞-valued sum is always defined, so no summability side condition can hold vacuously; the instances are the same
--   - encoding: a set 𝒜 ⊂ 𝒮 → A : Set S with A.Nonempty; reason: for A = ∅ there is nothing to condition on (π(j)/Σ_{k∈𝒜}π(k) is 0/0) and no process on an empty state space; this only excludes an undefined case
--   - reading: Y(t) is the stationary truncated process, and Y(−t) has the same transition rates as Z(t) → there is an equilibrium distribution μ of truncRates q A with μ(k)q(k,j)/μ(j) = π(k)q(k,j)/π(j) for all j, k ∈ A; reason: the rates of the reversed stationary process are given by Theorem 1.12; Y's equilibrium distribution is quantified (∃ μ), which is unique when the truncation is irreducible as the book requires
--   - generalization: truncation to 𝒜 requires the resulting process to be irreducible within the state space 𝒜 (p. 25) → no irreducibility assumption on the truncated rates truncRates q A; reason: the equivalence holds for every A; restricted to the A for which the truncated process is irreducible it is exactly the book's statement
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 33 (PDF p. 36), Exercise 1.7.7

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsKellyRates
import Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
import Definitions.Def_KellyRSN_PartialBalance_IsPartialBalance
import Definitions.Def_KellyRSN_PartialBalance_ReversalTruncationCommute

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Time reversal and truncation to `𝒜` commute iff partial balance holds.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.7.7, p. 33 (PDF p. 36):
"Suppose that a Markov process `X(t)` with transition rates `q(j, k)`, `j, k ∈ 𝒮`, and equilibrium
distribution `π(j)`, `j ∈ 𝒮`, is truncated to the set `𝒜`. Let `Y(t)` be the stationary truncated
process. Let `Z(t)` be the stationary process resulting from truncating the reversed process
`X(−t)` to the set `𝒜`. Show that `Z(t)` and `Y(−t)` have the same transition rates if and only if
the partial balance conditions (1.24) are satisfied."

**Formalization Note.** "Commute" is `ReversalTruncationCommute` (the book's definition in the same
exercise, with the reversed rates of Theorem 1.12). The irreducibility requirement on the truncated
process is not assumed; the equivalence holds without it. `A` is non-empty (a truncated process
on an empty state space has no equilibrium distribution). -/
theorem reversal_truncation_commute_iff
    {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) (hq : IsKellyRates q)
    (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) :
    ReversalTruncationCommute q π A ↔ IsPartialBalance q π A := by sorry

end KellyRSN.PartialBalance
