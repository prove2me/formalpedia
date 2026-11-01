-- Prove2me | Theorems.Thm_MaxWeightInstab_lemma_6
-- name    : MaxWeightInstab.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:13.691818+00:00
-- url     : https://prove2.me/theorems/ab24d613-d91d-4139-b6a6-9c098cf0096b
-- title:
--   Lemma 6 — component $\mathcal B$ stays nearly empty on $[U,V]$
-- statement:
--   Assume (4) and (5), let $\gamma$ satisfy (11), and assume (13) with $M$ satisfying (12). On the event $G_M$,
--
--   $$
--   Q^\Sigma_{\mathcal B}(t)\ \le\ \nu^3+\varepsilon bJT\qquad\text{for } t\in[U,V] . \tag{38}
--   $$
--
--   After time $U$ there are no arrivals at $\mathcal B_0$ (Lemma 4), and the quick queues $\mathcal B_1,\dots,\mathcal B_J$ are served faster than jobs arrive, so component $\mathcal B$ remains almost empty until $V$.
--
--   **Formalization Note** $\varepsilon_0,L$ depend only on $a,J,\nu,\gamma$; for each $\varepsilon\in(0,\varepsilon_0)$ there is $M_0$; times are integers.
--
--   Differences from the source:
--   - reading: ε ∈ (0, ε₀) and M ≥ L/ε (12) with ε₀, L depending only on a, J, ν, γ (p.6), M large enough that T ≥ C (p.7) and the proofs' "for large M" → ∃ ε₀, L > 0, ∀ ε ∈ (0, ε₀), ∃ M₀, ∀ M ≥ max(L/ε, M₀); reason: the quantifier order of pp.6–7; the per-ε threshold M₀ collects "T ≥ C" and the in-proof "for large M"
--   - encoding: "on the event G_M" for the random queue process → every MaxWeight trajectory (any tie choices) whose arrival path satisfies (15); reason: the statement is pathwise and G_M constrains the arrivals only; same content
--   - encoding: U, V := min{…} ∧ T (21) → first integer time at which the condition holds or t ≥ T (so ⌈T⌉ instead of T when the condition never holds before T); reason: Q(U), Q(V) must be defined; the two agree whenever the condition occurs before T, which (22) and Lemma 7 assert
--   - reading: γ: the section's standing choice satisfying (11) (pp.6–7), not restated in the lemma → hypothesis 1 < γ < a/(1 − a + aν/J); reason: γ enters G_M through b; standing assumption of §3.1
--   - reading: sup over 0 ≤ s ≤ t ≤ T in G_M (15), and the times t of the conclusion → integer times; reason: the process is indexed by t ∈ ℤ₊ (p.1, p.5) and (19) sums over t = 0, …, T
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Lemma 6, p.11

import Mathlib
import Definitions.Def_MaxWeightInstab_IsInitial
import Definitions.Def_MaxWeightInstab_IsGoodArrivals
import Definitions.Def_MaxWeightInstab_hitV

namespace MaxWeightInstab

/-- **Lemma 6** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.11). Assume (4) and (5), and assume (13) with `M` satisfying (12). On
the event `G_M`, `Q^Σ_ℬ(t) ≤ ν³ + εbJT` for `t ∈ [U, V]` (38).

**Formalization Note.** Quantifiers as on pp.6–7: the constants `ε₀`, `L` depend only on
`a, J, ν, γ` ("the constants ϵ₀, L, κ₁, ..., κ₄ will depend only on the parameters a, J, ν, and γ",
p.6); for each `ε ∈ (0, ε₀)` a threshold `M₀` collects "assume M to be sufficiently large so that
T ≥ C" (p.7) and the proofs' "for large M"; then the claim holds for every `M ≥ max(L/ε, M₀)` (12),
every MaxWeight trajectory (any tie choices) with `Q(0)` satisfying (13), and every arrival path in
`G_M` (15). `U`, `V` are the integer stopping times of (21) (`hitU`, `hitV`). -/
theorem lemma_6 (J ν : ℕ) (a γ : ℝ) (h4 : rRho a ν < 1)
    (h5ν : 1 < ν ∧ ν < J)
    (h5a : (J : ℝ) / (2 * J - ν) < a ∧
      a < 1 - ((J : ℝ) + ν) * ((J : ℝ) + (ν : ℝ) ^ 2) / ((ν : ℝ) * ((J : ℝ) ^ 2 + J + (ν : ℝ) ^ 2)))
    (h11 : 1 < γ ∧ γ < a / (1 - a + a * ν / J)) :
    ∃ ε₀ > 0, ∃ L > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → L / ε ≤ M →
      ∀ tr : Trajectory J ν, IsInitial ν ε M (tr.Q 0) → IsGoodArrivals a J ν γ ε M tr.e →
        ∀ t : ℕ, hitU tr (horizon a ν M) ≤ t → t ≤ hitV tr (horizon a ν M) →
          (totalB (tr.Q t) : ℝ) ≤ (ν : ℝ) ^ 3 + ε * bConst a J ν γ * J * horizon a ν M := by sorry

end MaxWeightInstab
