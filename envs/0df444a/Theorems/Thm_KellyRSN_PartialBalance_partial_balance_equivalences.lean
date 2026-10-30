-- Prove2me | Theorems.Thm_KellyRSN_PartialBalance_partial_balance_equivalences
-- name    : KellyRSN.PartialBalance.partial_balance_equivalences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:28.758099+00:00
-- url     : https://prove2.me/theorems/8c08023d-e219-40f4-9502-13de083abc8c
-- title:
--   Theorem 9.5 — six equivalent characterizations of partial balance
-- statement:
--   Let $q(j,k)$, $j,k \in \mathcal S$, be the transition rates of a Markov process on a countable state space $\mathcal S$ satisfying the standing assumptions of §1.1 ($q(j,j) = 0$, $q(j) = \sum_k q(j,k) < \infty$, irreducible, non-explosive), and let $\pi(j)$, $j \in \mathcal S$, be its equilibrium distribution.
--   Let $\mathcal A \subseteq \mathcal S$ be non-empty. The following statements are equivalent:
--
--   1. (i) $\pi$ satisfies the partial balance conditions
--   $$
--   \pi(j) \sum_{k \in \mathcal A} q(j,k) = \sum_{k \in \mathcal A} \pi(k)\, q(k,j), \qquad j \in \mathcal A .
--   $$
--   2. (ii) The conditional distribution $\pi(j) / \sum_{k \in \mathcal A} \pi(k)$, $j \in \mathcal A$, is the equilibrium distribution of the process truncated to $\mathcal A$.
--   3. (iii) For every real $c > 0$, $c \ne 1$: after changing $q(j,k)$ to $c\,q(j,k)$ for $j, k \in \mathcal A$, the process still has equilibrium distribution $\pi$.
--   4. (iv) For every real $c > 0$, $c \ne 1$: after changing $q(j,k)$ to $c\,q(j,k)$ for $j \in \mathcal A$, $k \in \mathcal S - \mathcal A$, the equilibrium distribution of the process is $B\pi(j)$ for $j \in \mathcal A$ and $Bc\,\pi(j)$ for $j \in \mathcal S - \mathcal A$, for a constant $B$.
--   5. (v) The operations of time reversal and truncation to $\mathcal A$ commute.
--
--   If in addition $\mathcal S - \mathcal A$ is non-empty and the probability flux $\sum_{j \in \mathcal A} \sum_{k \in \mathcal S - \mathcal A} \pi(j) q(j,k)$ is finite, then (i)–(v) are also equivalent to
--
--   6. (vi) The Markov chain formed by observing the process just before it leaves $\mathcal A$ has the same equilibrium distribution as the Markov chain formed by observing the process just after it enters $\mathcal A$.
--
--   The theorem shows that partial balance, a condition intermediate between detailed balance and the full equilibrium equations, is exactly the condition under which conditioning, local speed changes, time reversal and the boundary behaviour of a set interact simply; it underlies the insensitivity properties of many stochastic network models.
--
--   **Formalization Note** The conclusion is the conjunction of the equivalences of (i) with each of (ii)–(vi), (iii) and (iv) for each admissible $c$. "The equilibrium distribution of the truncated/altered process is $\rho$" is stated as "$\rho$ is an equilibrium distribution" of those rates.
--
--   Differences from the source:
--   - encoding: a (continuous-time) Markov process with transition rates q(j, k) on a countable state space, under the standing assumptions of §1.1 (time homogeneous, irreducible, positive holding times, non-explosive) → a rate matrix q : S → S → ℝ≥0∞ on a countable S with IsKellyRates q (q(j,j) = 0, q(j) < ∞, irreducible, non-explosive in the form Σ_n 1/q(J_n) = ∞ almost surely along the jump chain); reason: the book never constructs the process from its rates and every statement is about the rates, the equilibrium equations and the jump chain; non-explosion is equivalent to Σ_n 1/q(J_n) = ∞ a.s. (Norris, Markov Chains, Thms 2.3.2 and 2.7.1)
--   - encoding: real rates, probabilities and sums → values and tsums in ℝ≥0∞; reason: an ℝ≥0∞-valued sum is always defined, so no summability side condition can hold vacuously; the instances are the same
--   - encoding: a set 𝒜 ⊂ 𝒮 → A : Set S with A.Nonempty; reason: for A = ∅ there is nothing to condition on (π(j)/Σ_{k∈𝒜}π(k) is 0/0) and no process on an empty state space; this only excludes an undefined case
--   - reading: the equilibrium distribution of the truncated process is the conditional distribution → condDist π A is an equilibrium distribution (IsEquilibriumDist) of truncRates q A; reason: the book defines an equilibrium distribution as a positive solution of (1.3) summing to one and states it is unique when it exists (p. 3); the Lean does not assume the truncated process non-explosive, and for an irreducible truncation 'is an' and 'is the' coincide
--   - reading: the resulting process has the same (unaltered) equilibrium distribution π → π is an equilibrium distribution (IsEquilibriumDist) of scaleInside q A c; reason: an equilibrium distribution is unique when it exists (p. 3); the Lean does not assume the altered process non-explosive, so it states the equilibrium equations, positivity and normalization directly
--   - reading: the equilibrium distribution of the resulting process takes the form Bπ(j), Bcπ(j) → that function is an equilibrium distribution (IsEquilibriumDist) of scaleOutward q A c for some B; reason: an equilibrium distribution is unique when it exists (p. 3); Exercise 1.6.4 itself says 'has an equilibrium distribution of the form'
--   - reading: Y(t) is the stationary truncated process, and Y(−t) has the same transition rates as Z(t) → there is an equilibrium distribution μ of truncRates q A with μ(k)q(k,j)/μ(j) = π(k)q(k,j)/π(j) for all j, k ∈ A; reason: the rates of the reversed stationary process are given by Theorem 1.12; Y's equilibrium distribution is quantified (∃ μ), which is unique when the truncation is irreducible as the book requires
--   - generalization: truncation to 𝒜 requires the resulting process to be irreducible within the state space 𝒜 (p. 25) → no irreducibility assumption on the truncated rates truncRates q A; reason: the equivalence holds for every A; restricted to the A for which the truncated process is irreducible it is exactly the book's statement
--   - encoding: c ≠ 0 or 1 → c : ℝ≥0 with c ≠ 0 and c ≠ 1, the equivalence asserted for each such c; reason: rates are non-negative real numbers, so only c > 0 gives a Markov process; the book's statement is for an arbitrary such c
--   - encoding: Bπ(j), j ∈ 𝒜; Bcπ(j), j ∈ 𝒮 − 𝒜, with B a normalizing constant → ∃ B : ℝ≥0∞ such that (j ↦ if j ∈ A then B π j else B c π j) is an equilibrium distribution; reason: summing to one forces B⁻¹ = Σ_{j∈𝒜} π(j) + c Σ_{j∈𝒮−𝒜} π(j) (Lemma 1.9's constant, p. 25), so the existential loses nothing
--   - encoding: the Markov chains formed by observing the process just before it leaves 𝒜 and just after it enters 𝒜, and 'has the same equilibrium distribution' → kernels exitKernel q A and entryKernel q A on ↥A read off the jump chain law; SameObservedEquilibrium: each kernel has exactly one stationary probability vector (IsStationaryProb) and the two coincide; vectors vanish on states of A the chain never visits; reason: the process leaves and enters 𝒜 only at jumps, so the observed states are those of the jump chain at its exit and entry steps; 'the' equilibrium distribution follows the book's convention that it is unique when it exists; the chains live on the states with a positive rate out of (into) 𝒜 and their distributions are extended by 0 to the rest of A
--   - encoding: (vi) for a set 𝒜 ⊂ 𝒮 → additional hypothesis (Aᶜ).Nonempty; reason: for A = S the process never leaves or enters A and the two observed chains do not exist; this only excludes an undefined case
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 200-201 (PDF pp. 203-204), Theorem 9.5

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsKellyRates
import Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
import Definitions.Def_KellyRSN_PartialBalance_IsPartialBalance
import Definitions.Def_KellyRSN_PartialBalance_truncRates
import Definitions.Def_KellyRSN_PartialBalance_condDist
import Definitions.Def_KellyRSN_PartialBalance_scaleInside
import Definitions.Def_KellyRSN_PartialBalance_scaleOutward
import Definitions.Def_KellyRSN_PartialBalance_ReversalTruncationCommute
import Definitions.Def_KellyRSN_PartialBalance_fluxOut
import Definitions.Def_KellyRSN_PartialBalance_SameObservedEquilibrium

open scoped ENNReal NNReal

namespace KellyRSN.PartialBalance

open Classical in
/-- **Theorem 9.5 — six equivalent characterizations of partial balance.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Theorem 9.5, pp. 200–201
(PDF pp. 203–204): "For a Markov process with transition rates `q(j, k)`, `j, k ∈ 𝒮`, and
equilibrium distribution `π(j)`, `j ∈ 𝒮`, the following statements are equivalent:
(i) The distribution `π(j)`, `j ∈ 𝒮`, satisfies the partial balance conditions
`π(j) Σ_{k∈𝒜} q(j, k) = Σ_{k∈𝒜} π(k) q(k, j)`, `j ∈ 𝒜`.
(ii) If the process is truncated to the set `𝒜` the equilibrium distribution of the truncated
process is the conditional probability distribution `π(j) / Σ_{k∈𝒜} π(k)`, `j ∈ 𝒜`.
(iii) If the process is altered by changing the transition rate `q(j, k)` to `c q(j, k)` for
`j, k ∈ 𝒜`, where `c ≠ 0` or `1`, then the resulting process has the unaltered equilibrium
distribution `π(j)`, `j ∈ 𝒮`.
(iv) If the process is altered by changing the transition rate `q(j, k)` to `c q(j, k)` for
`j ∈ 𝒜`, `k ∈ 𝒮 − 𝒜`, where `c ≠ 0` or `1`, then the equilibrium distribution of the resulting
process takes the form `Bπ(j)`, `j ∈ 𝒜`; `Bcπ(j)`, `j ∈ 𝒮 − 𝒜`.
(v) The operations of time reversal and truncation to the set `𝒜` commute.
If in addition `Σ_{j∈𝒜} Σ_{k∈𝒮−𝒜} π(j) q(j, k)` is finite, then statements (i) to (v) are
equivalent to:
(vi) The Markov chain formed by observing the process at those instants in time just before it
leaves the set `𝒜` has the same equilibrium distribution as the Markov chain formed by observing
the process at those instants in time just after it enters the set `𝒜`."

The conclusion is the conjunction of the equivalences of (i) with each of (ii)–(vi).

**Formalization Note.** The Markov process is its rate matrix `q` on a countable `S` with all the
standing assumptions of §1.1 (`IsKellyRates`: `q(j, j) = 0`, `q(j) < ∞`, irreducible,
non-explosive). Rates, distributions, `B` and all sums are in `ℝ≥0∞`; `c : ℝ≥0`. "The equilibrium
distribution of the truncated / altered process is `ρ`" is stated as "`ρ` is an equilibrium
distribution of those rates" (unique under the book's standing assumptions, p. 3); the
truncated process is not required to be irreducible. (iii) and (iv) hold for each `c ≠ 0, 1`.
`A` is non-empty, and for (vi) also `𝒮 − 𝒜`: otherwise the conditional distribution, respectively
the exit and entry chains, do not exist. -/
theorem partial_balance_equivalences
    {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) (hq : IsKellyRates q)
    (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) :
    (IsPartialBalance q π A ↔ IsEquilibriumDist (truncRates q A) (condDist π A)) ∧
    (∀ c : ℝ≥0, c ≠ 0 → c ≠ 1 →
      (IsPartialBalance q π A ↔ IsEquilibriumDist (scaleInside q A c) π)) ∧
    (∀ c : ℝ≥0, c ≠ 0 → c ≠ 1 →
      (IsPartialBalance q π A ↔ ∃ B : ℝ≥0∞, IsEquilibriumDist (scaleOutward q A c)
        (fun j => if j ∈ A then B * π j else B * (c : ℝ≥0∞) * π j))) ∧
    (IsPartialBalance q π A ↔ ReversalTruncationCommute q π A) ∧
    (fluxOut q π A ≠ ⊤ → (Aᶜ).Nonempty →
      (IsPartialBalance q π A ↔ SameObservedEquilibrium q A)) := by sorry

end KellyRSN.PartialBalance
