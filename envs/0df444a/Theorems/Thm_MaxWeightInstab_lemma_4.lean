-- Prove2me | Theorems.Thm_MaxWeightInstab_lemma_4
-- name    : MaxWeightInstab.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:44.191133+00:00
-- url     : https://prove2.me/theorems/40245f45-644b-42ec-ab22-f5c58c77e612
-- title:
--   Lemma 4 — only $\mathcal A_0$ is served at component $\mathcal A$ on $(U\wedge\varepsilon\kappa_2M,V]$
-- statement:
--   Assume (4) and (5), let $\gamma$ satisfy (11), and assume (13) with $M$ satisfying (12). On the event $G_M$ there is a sufficiently large $\kappa_2$ such that
--
--   $$
--   Q_{\mathcal A_0}(t)\ >\ \nu\max_{j=1,\dots,J}Q_{\mathcal A_j}(t)\qquad\text{for } t\in[U\wedge\varepsilon\kappa_2M,\,V) . \tag{32}
--   $$
--
--   In particular, in every time unit $t\in(U\wedge\varepsilon\kappa_2M,V]$ only queue $\mathcal A_0$ is served at component $\mathcal A$: the MaxWeight schedule gives one unit of service to $\mathcal A_0$ and none to $\mathcal A_1,\dots,\mathcal A_J$.
--
--   This is the step that starves the externally fed queues of component $\mathcal A$, so that they grow linearly while $\mathcal A_0$ is drained.
--
--   **Formalization Note** $\varepsilon_0,L,\kappa_2$ depend only on $a,J,\nu,\gamma$; for each $\varepsilon\in(0,\varepsilon_0)$ there is $M_0$. The schedule of time unit $t$ is the one chosen for $Q(t-1)$.
--
--   Differences from the source:
--   - reading: ε ∈ (0, ε₀) and M ≥ L/ε (12) with ε₀, L, κ₂ depending only on a, J, ν, γ (p.6), M large enough that T ≥ C (p.7) and the proofs' "for large M" → ∃ ε₀, L, κ₂ > 0, ∀ ε ∈ (0, ε₀), ∃ M₀, ∀ M ≥ max(L/ε, M₀); reason: the quantifier order of pp.6–7; the per-ε threshold M₀ collects "T ≥ C" and the in-proof "for large M"
--   - encoding: "on the event G_M" for the random queue process → every MaxWeight trajectory (any tie choices) whose arrival path satisfies (15); reason: the statement is pathwise and G_M constrains the arrivals only; same content
--   - encoding: U, V := min{…} ∧ T (21) → first integer time at which the condition holds or t ≥ T (so ⌈T⌉ instead of T when the condition never holds before T); reason: Q(U), Q(V) must be defined; the two agree whenever the condition occurs before T, which (22) and Lemma 7 assert
--   - reading: "only Queue 𝒜₀ is served at Component 𝒜" on (U ∧ εκ₂M, V] → the schedule of each such time unit is 1 at 𝒜₀ and 0 at 𝒜₁, …, 𝒜_J; reason: the strongest reading; under (32) it is the unique MaxWeight choice on component 𝒜
--   - reading: γ: the section's standing choice satisfying (11) (pp.6–7), not restated in the lemma → hypothesis 1 < γ < a/(1 − a + aν/J); reason: γ enters G_M through b; standing assumption of §3.1
--   - reading: sup over 0 ≤ s ≤ t ≤ T in G_M (15), and the times t of the conclusion → integer times; reason: the process is indexed by t ∈ ℤ₊ (p.1, p.5) and (19) sums over t = 0, …, T
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Lemma 4, p.10

import Mathlib
import Definitions.Def_MaxWeightInstab_IsInitial
import Definitions.Def_MaxWeightInstab_IsGoodArrivals
import Definitions.Def_MaxWeightInstab_hitV

namespace MaxWeightInstab

/-- **Lemma 4** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.10). Assume (4) and (5), and assume (13) with `M` satisfying (12). On
the event `G_M`, there exists a sufficiently large `κ₂` such that, for `t ∈ [U ∧ εκ₂M, V)`,
`Q_{𝒜₀}(t) > ν max_{j=1,…,J} Q_{𝒜_j}(t)` (32). In particular, on `(U ∧ εκ₂M, V]`, only Queue
`𝒜₀` is served at Component `𝒜`.

**Formalization Note.** Quantifiers as on pp.6–7: the constants `ε₀`, `L`, `κ₂` depend only on
`a, J, ν, γ` ("the constants ϵ₀, L, κ₁, ..., κ₄ will depend only on the parameters a, J, ν, and γ",
p.6); for each `ε ∈ (0, ε₀)` a threshold `M₀` collects "assume M to be sufficiently large so that
T ≥ C" (p.7) and the proofs' "for large M"; then the claim holds for every `M ≥ max(L/ε, M₀)` (12),
every MaxWeight trajectory (any tie choices) with `Q(0)` satisfying (13), and every arrival path in
`G_M` (15). `U`, `V` are the integer stopping times of (21) (`hitU`, `hitV`). "Only Queue 𝒜₀ is served at Component 𝒜" in time unit `t` is stated
on the schedule `σ(t)` of that time unit (governed by `Q(t − 1)`, p.10): it gives one unit of
service to `𝒜₀` and none to `𝒜₁, …, 𝒜_J`. -/
theorem lemma_4 (J ν : ℕ) (a γ : ℝ) (h4 : rRho a ν < 1)
    (h5ν : 1 < ν ∧ ν < J)
    (h5a : (J : ℝ) / (2 * J - ν) < a ∧
      a < 1 - ((J : ℝ) + ν) * ((J : ℝ) + (ν : ℝ) ^ 2) / ((ν : ℝ) * ((J : ℝ) ^ 2 + J + (ν : ℝ) ^ 2)))
    (h11 : 1 < γ ∧ γ < a / (1 - a + a * ν / J)) :
    ∃ ε₀ > 0, ∃ L > 0, ∃ κ₂ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → L / ε ≤ M →
      ∀ tr : Trajectory J ν, IsInitial ν ε M (tr.Q 0) → IsGoodArrivals a J ν γ ε M tr.e →
        (∀ t : ℕ, min (hitU tr (horizon a ν M) : ℝ) (ε * κ₂ * M) ≤ t → t < hitV tr (horizon a ν M) →
          ν * maxA (tr.Q t) < tr.Q t (Sum.inl 0)) ∧
        (∀ t : ℕ, min (hitU tr (horizon a ν M) : ℝ) (ε * κ₂ * M) < t → t ≤ hitV tr (horizon a ν M) →
          tr.σ t (Sum.inl 0) = 1 ∧ ∀ j : Fin J, tr.σ t (Sum.inl j.succ) = 0) := by sorry

end MaxWeightInstab
