-- Prove2me | Theorems.Thm_MaxWeightInstab_proposition_1
-- name    : MaxWeightInstab.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:17.089461+00:00
-- url     : https://prove2.me/theorems/dcd3b666-b9a9-42f6-9de9-d32f6145d4d0
-- title:
--   Proposition 1 — after one half-cycle the roles of $\mathcal A$ and $\mathcal B$ are reversed with $M'=\gamma M$
-- statement:
--   Assume (4) and (5), let $\gamma$ satisfy (11), and assume (13) with $M$ satisfying (12). Then, on the event $G_M$, with $M'=\gamma M$ and $V$ the stopping time of (21), which satisfies $0<V\le T$:
--
--   1. $Q^\Sigma_{\mathcal A}(V)\ge M'$ (17a);
--   2. $Q^\Sigma_{\mathcal B}(V)\le\varepsilon M'/\nu$ (17b);
--   3. $|Q_{\mathcal A_0}(V)-\nu Q_{\mathcal A_j}(V)|\le\varepsilon M'$ for $j=1,\dots,J$ (17c);
--   4. for all times $0\le t\le V$,
--
--   $$
--   Q^\Sigma_{\mathcal A}(t)+Q^\Sigma_{\mathcal B}(t)\ \ge\ \frac12\,\frac{a}{a+\nu}\,M . \tag{18}
--   $$
--
--   At time $V$ the mirror image of the initial condition (13) holds with $M$ replaced by $\gamma M>M$: the work in the network has grown by the factor $\gamma$, and it never dropped below a fixed fraction of $M$ meanwhile.
--
--   **Formalization Note** $\varepsilon_0,L$ depend only on $a,J,\nu,\gamma$; for each $\varepsilon\in(0,\varepsilon_0)$ there is $M_0$.
--
--   Differences from the source:
--   - reading: ε ∈ (0, ε₀) and M ≥ L/ε (12) with ε₀, L depending only on a, J, ν, γ (p.6), M large enough that T ≥ C (p.7) and the proofs' "for large M" → ∃ ε₀, L > 0, ∀ ε ∈ (0, ε₀), ∃ M₀, ∀ M ≥ max(L/ε, M₀); reason: the quantifier order of pp.6–7; the per-ε threshold M₀ collects "T ≥ C" and the in-proof "for large M"
--   - encoding: "on the event G_M" for the random queue process → every MaxWeight trajectory (any tie choices) whose arrival path satisfies (15); reason: the statement is pathwise and G_M constrains the arrivals only; same content
--   - encoding: U, V := min{…} ∧ T (21) → first integer time at which the condition holds or t ≥ T (so ⌈T⌉ instead of T when the condition never holds before T); reason: Q(U), Q(V) must be defined; the two agree whenever the condition occurs before T, which (22) and Lemma 7 assert
--   - encoding: "V is a stopping time satisfying 0 < V ≤ T" (definitional for min{…} ∧ T) → 0 < V and V ≤ T stated as conclusions; reason: with the integer V capped at ⌈T⌉ the bound V ≤ T is no longer automatic; it follows from Lemma 7's V < T
--   - reading: γ: the section's standing choice satisfying (11) (pp.6–7), not restated in the lemma → hypothesis 1 < γ < a/(1 − a + aν/J); reason: γ enters G_M through b; standing assumption of §3.1
--   - reading: sup over 0 ≤ s ≤ t ≤ T in G_M (15), and the times t of the conclusion → integer times; reason: the process is indexed by t ∈ ℤ₊ (p.1, p.5) and (19) sums over t = 0, …, T
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Proposition 1, p.7

import Mathlib
import Definitions.Def_MaxWeightInstab_IsInitial
import Definitions.Def_MaxWeightInstab_IsGoodArrivals
import Definitions.Def_MaxWeightInstab_hitV

namespace MaxWeightInstab

/-- **Proposition 1** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.7). Assume (4) and (5), and assume (13) with `M` satisfying (12).
Then, on the event `G_M`, `Q^Σ_𝒜(V) ≥ M′` (17a), `Q^Σ_ℬ(V) ≤ εM′/ν` (17b),
`|Q_{𝒜₀}(V) − νQ_{𝒜_j}(V)| ≤ εM′` (17c) for `j = 1, …, J`, where `V` is the stopping time of (21)
satisfying `0 < V ≤ T` and `M′ = γM`. Moreover, for all times `0 ≤ t ≤ V`,
`Q^Σ_𝒜(t) + Q^Σ_ℬ(t) ≥ (1/2)(a/(a + ν)) M` (18).

**Formalization Note.** Quantifiers as on pp.6–7: the constants `ε₀`, `L` depend only on
`a, J, ν, γ` ("the constants ϵ₀, L, κ₁, ..., κ₄ will depend only on the parameters a, J, ν, and γ",
p.6); for each `ε ∈ (0, ε₀)` a threshold `M₀` collects "assume M to be sufficiently large so that
T ≥ C" (p.7) and the proofs' "for large M"; then the claim holds for every `M ≥ max(L/ε, M₀)` (12),
every MaxWeight trajectory (any tie choices) with `Q(0)` satisfying (13), and every arrival path in
`G_M` (15). `U`, `V` are the integer stopping times of (21) (`hitU`, `hitV`). With the integer `V` of `hitV` (capped at `⌈T⌉`), `0 < V ≤ T` is a
conclusion rather than part of the definition. -/
theorem proposition_1 (J ν : ℕ) (a γ : ℝ) (h4 : rRho a ν < 1)
    (h5ν : 1 < ν ∧ ν < J)
    (h5a : (J : ℝ) / (2 * J - ν) < a ∧
      a < 1 - ((J : ℝ) + ν) * ((J : ℝ) + (ν : ℝ) ^ 2) / ((ν : ℝ) * ((J : ℝ) ^ 2 + J + (ν : ℝ) ^ 2)))
    (h11 : 1 < γ ∧ γ < a / (1 - a + a * ν / J)) :
    ∃ ε₀ > 0, ∃ L > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → L / ε ≤ M →
      ∀ tr : Trajectory J ν, IsInitial ν ε M (tr.Q 0) → IsGoodArrivals a J ν γ ε M tr.e →
        γ * M ≤ (totalA (tr.Q (hitV tr (horizon a ν M))) : ℝ) ∧
        (totalB (tr.Q (hitV tr (horizon a ν M))) : ℝ) ≤ ε * (γ * M) / ν ∧
        (∀ j : Fin J, |(tr.Q (hitV tr (horizon a ν M)) (Sum.inl 0) : ℝ) - ν * (tr.Q (hitV tr (horizon a ν M)) (Sum.inl j.succ) : ℝ)| ≤
          ε * (γ * M)) ∧
        0 < hitV tr (horizon a ν M) ∧ (hitV tr (horizon a ν M) : ℝ) ≤ horizon a ν M ∧
        ∀ t : ℕ, t ≤ hitV tr (horizon a ν M) →
          1 / 2 * (a / (a + ν)) * M ≤ (totalA (tr.Q t) : ℝ) + totalB (tr.Q t) := by sorry

end MaxWeightInstab
