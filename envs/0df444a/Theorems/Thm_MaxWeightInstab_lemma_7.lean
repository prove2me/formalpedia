-- Prove2me | Theorems.Thm_MaxWeightInstab_lemma_7
-- name    : MaxWeightInstab.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:11.73532+00:00
-- url     : https://prove2.me/theorems/67528af4-70ee-4f62-9f60-9faf68c82183
-- title:
--   Lemma 7 — the time $V$ and the mass $Q^\Sigma_{\mathcal A}(V)$
-- statement:
--   Assume (4) and (5), let $\gamma$ satisfy (11), and assume (13) with $M$ satisfying (12). On the event $G_M$ there exist constants $\kappa_3>0$ and $\kappa_4>0$ such that
--
--   $$
--   \left|V-\frac{JM}{J+\nu}\cdot\frac{1}{1-a+a\nu/J}\right|\ \le\ \varepsilon\kappa_3M , \tag{40}
--   $$
--
--   $$
--   Q^\Sigma_{\mathcal A}(V)\ \ge\ \frac{aM}{1-a+a\nu/J}-\varepsilon\kappa_4M , \tag{41}
--   $$
--
--   and, by (40), $V<T$ for sufficiently small $\varepsilon>0$.
--
--   The lemma pins down the end $V$ of the half-cycle and the number of jobs then at component $\mathcal A$, which exceeds $\gamma M$ by (11).
--
--   **Formalization Note** $\varepsilon_0,L,\kappa_3,\kappa_4$ depend only on $a,J,\nu,\gamma$ ($\varepsilon_0$ small enough for $V<T$); for each $\varepsilon\in(0,\varepsilon_0)$ there is $M_0$.
--
--   Differences from the source:
--   - reading: ε ∈ (0, ε₀) and M ≥ L/ε (12) with ε₀, L, κ₃, κ₄ depending only on a, J, ν, γ (p.6), M large enough that T ≥ C (p.7) and the proofs' "for large M" → ∃ ε₀, L, κ₃, κ₄ > 0, ∀ ε ∈ (0, ε₀), ∃ M₀, ∀ M ≥ max(L/ε, M₀); reason: the quantifier order of pp.6–7; the per-ε threshold M₀ collects "T ≥ C" and the in-proof "for large M"
--   - encoding: "on the event G_M" for the random queue process → every MaxWeight trajectory (any tie choices) whose arrival path satisfies (15); reason: the statement is pathwise and G_M constrains the arrivals only; same content
--   - encoding: U, V := min{…} ∧ T (21) → first integer time at which the condition holds or t ≥ T (so ⌈T⌉ instead of T when the condition never holds before T); reason: Q(U), Q(V) must be defined; the two agree whenever the condition occurs before T, which (22) and Lemma 7 assert
--   - reading: the sentence after the lemma, "By (40), V < T for sufficiently small ϵ > 0" → a third conclusion V < T; reason: it is part of the italic statement block and is used by Proposition 1
--   - reading: γ: the section's standing choice satisfying (11) (pp.6–7), not restated in the lemma → hypothesis 1 < γ < a/(1 − a + aν/J); reason: γ enters G_M through b; standing assumption of §3.1
--   - reading: sup over 0 ≤ s ≤ t ≤ T in G_M (15), and the times t of the conclusion → integer times; reason: the process is indexed by t ∈ ℤ₊ (p.1, p.5) and (19) sums over t = 0, …, T
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Lemma 7, p.12

import Mathlib
import Definitions.Def_MaxWeightInstab_IsInitial
import Definitions.Def_MaxWeightInstab_IsGoodArrivals
import Definitions.Def_MaxWeightInstab_hitV

namespace MaxWeightInstab

/-- **Lemma 7** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.12). Assume (4) and (5), and assume (13) with `M` satisfying (12). On
the event `G_M`, there exist constants `κ₃ > 0` and `κ₄ > 0` satisfying
`|V − (JM/(J + ν)) · 1/(1 − a + aν/J)| ≤ εκ₃M` (40) and
`Q^Σ_𝒜(V) ≥ aM/(1 − a + aν/J) − εκ₄M` (41). By (40), `V < T` for sufficiently small `ε > 0`.

**Formalization Note.** Quantifiers as on pp.6–7: the constants `ε₀`, `L`, `κ₃`, `κ₄` depend only on
`a, J, ν, γ` ("the constants ϵ₀, L, κ₁, ..., κ₄ will depend only on the parameters a, J, ν, and γ",
p.6); for each `ε ∈ (0, ε₀)` a threshold `M₀` collects "assume M to be sufficiently large so that
T ≥ C" (p.7) and the proofs' "for large M"; then the claim holds for every `M ≥ max(L/ε, M₀)` (12),
every MaxWeight trajectory (any tie choices) with `Q(0)` satisfying (13), and every arrival path in
`G_M` (15). `U`, `V` are the integer stopping times of (21) (`hitU`, `hitV`). The sentence after the lemma, `V < T`, is the third clause
(`ε₀` small enough). -/
theorem lemma_7 (J ν : ℕ) (a γ : ℝ) (h4 : rRho a ν < 1)
    (h5ν : 1 < ν ∧ ν < J)
    (h5a : (J : ℝ) / (2 * J - ν) < a ∧
      a < 1 - ((J : ℝ) + ν) * ((J : ℝ) + (ν : ℝ) ^ 2) / ((ν : ℝ) * ((J : ℝ) ^ 2 + J + (ν : ℝ) ^ 2)))
    (h11 : 1 < γ ∧ γ < a / (1 - a + a * ν / J)) :
    ∃ ε₀ > 0, ∃ L > 0, ∃ κ₃ > 0, ∃ κ₄ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → L / ε ≤ M →
      ∀ tr : Trajectory J ν, IsInitial ν ε M (tr.Q 0) → IsGoodArrivals a J ν γ ε M tr.e →
        |(hitV tr (horizon a ν M) : ℝ) - (J : ℝ) * M / ((J : ℝ) + ν) * (1 / (1 - a + a * ν / J))| ≤ ε * κ₃ * M ∧
        a * M / (1 - a + a * ν / J) - ε * κ₄ * M ≤ (totalA (tr.Q (hitV tr (horizon a ν M))) : ℝ) ∧
        (hitV tr (horizon a ν M) : ℝ) < horizon a ν M := by sorry

end MaxWeightInstab
