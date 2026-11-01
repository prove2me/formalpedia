-- Prove2me | Theorems.Thm_MaxWeightInstab_lemma_3
-- name    : MaxWeightInstab.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:22.012557+00:00
-- url     : https://prove2.me/theorems/d9ab41a8-e2a1-47df-8691-5cbcd78ffb16
-- title:
--   Lemma 3 — $\mathcal A_0$ receives jobs at rate $\nu(1-a)(1-\nu^2/(\nu^2+J))$ up to time $U$
-- statement:
--   Assume (4), let $\gamma$ satisfy (11), and assume (13) with $M$ satisfying (12). On the event $G_M$ there is a constant $\kappa_1>0$ such that, for $t\le U$,
--
--   $$
--   A_{\mathcal A_0}(t)\ \ge\ \nu(1-a)\left(1-\frac{\nu^2}{\nu^2+J}\right)t-\varepsilon\kappa_1M . \tag{26}
--   $$
--
--   Here $A_{\mathcal A_0}(t)=\sum_{j=1}^JD_{\mathcal B_j}(t)$ is the number of jobs routed from $\mathcal B_1,\dots,\mathcal B_J$ to $\mathcal A_0$ by time $t$. While component $\mathcal B$ is busy and balanced, a fixed fraction of its service goes to the quick queues $\mathcal B_1,\dots,\mathcal B_J$, and this feeds $\mathcal A_0$ at a linear rate.
--
--   **Formalization Note** $\varepsilon_0,L,\kappa_1$ depend only on $a,J,\nu,\gamma$; for each $\varepsilon\in(0,\varepsilon_0)$ there is $M_0$, and the bound holds for all $M\ge\max(L/\varepsilon,M_0)$, all MaxWeight trajectories with $Q(0)\in\mathcal I_M$, all arrival paths in $G_M$ and all integer $t\le U$.
--
--   Differences from the source:
--   - reading: ε ∈ (0, ε₀) and M ≥ L/ε (12) with ε₀, L, κ₁ depending only on a, J, ν, γ (p.6), M large enough that T ≥ C (p.7) and the proofs' "for large M" → ∃ ε₀, L, κ₁ > 0, ∀ ε ∈ (0, ε₀), ∃ M₀, ∀ M ≥ max(L/ε, M₀); reason: the quantifier order of pp.6–7; the per-ε threshold M₀ collects "T ≥ C" and the in-proof "for large M"
--   - encoding: "on the event G_M" for the random queue process → every MaxWeight trajectory (any tie choices) whose arrival path satisfies (15); reason: the statement is pathwise and G_M constrains the arrivals only; same content
--   - encoding: U, V := min{…} ∧ T (21) → first integer time at which the condition holds or t ≥ T (so ⌈T⌉ instead of T when the condition never holds before T); reason: Q(U), Q(V) must be defined; the two agree whenever the condition occurs before T, which (22) and Lemma 7 assert
--   - reading: γ: the section's standing choice satisfying (11) (pp.6–7), not restated in the lemma → hypothesis 1 < γ < a/(1 − a + aν/J); reason: γ enters G_M through b; standing assumption of §3.1
--   - encoding: J ∈ ℤ₊, ν ∈ ℕ with 1/ν in (3)–(4) → 0 < J and 0 < ν; reason: excludes only the cases where a/J or 1/ν is undefined
--   - reading: sup over 0 ≤ s ≤ t ≤ T in G_M (15), and the times t of the conclusion → integer times; reason: the process is indexed by t ∈ ℤ₊ (p.1, p.5) and (19) sums over t = 0, …, T
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Lemma 3, p.9

import Mathlib
import Definitions.Def_MaxWeightInstab_IsInitial
import Definitions.Def_MaxWeightInstab_IsGoodArrivals
import Definitions.Def_MaxWeightInstab_hitU
import Definitions.Def_MaxWeightInstab_cumArrivals

namespace MaxWeightInstab

/-- **Lemma 3** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.9). Assume (4), and assume (13) with `M` satisfying (12). On the
event `G_M`, there exists a constant `κ₁ > 0` such that, for `t ≤ U`,
`A_{𝒜₀}(t) ≥ ν(1 − a)(1 − ν²/(ν² + J)) t − εκ₁M` (26).

**Formalization Note.** Quantifiers as on pp.6–7: the constants `ε₀`, `L`, `κ₁` depend only on
`a, J, ν, γ` ("the constants ϵ₀, L, κ₁, ..., κ₄ will depend only on the parameters a, J, ν, and γ",
p.6); for each `ε ∈ (0, ε₀)` a threshold `M₀` collects "assume M to be sufficiently large so that
T ≥ C" (p.7) and the proofs' "for large M"; then the claim holds for every `M ≥ max(L/ε, M₀)` (12),
every MaxWeight trajectory (any tie choices) with `Q(0)` satisfying (13), and every arrival path in
`G_M` (15). `U`, `V` are the integer stopping times of (21) (`hitU`, `hitV`). `A_{𝒜₀}(t) = ∑_{j≥1} D_{ℬ_j}(t)` (`cumArrivals`). The section's `γ`
with (11) is assumed; `J, ν ≥ 1`. -/
theorem lemma_3 (J ν : ℕ) (a γ : ℝ) (hJ : 0 < J) (hν : 0 < ν) (h4 : rRho a ν < 1)
    (h11 : 1 < γ ∧ γ < a / (1 - a + a * ν / J)) :
    ∃ ε₀ > 0, ∃ L > 0, ∃ κ₁ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → L / ε ≤ M →
      ∀ tr : Trajectory J ν, IsInitial ν ε M (tr.Q 0) → IsGoodArrivals a J ν γ ε M tr.e →
        ∀ t : ℕ, t ≤ hitU tr (horizon a ν M) →
          (ν : ℝ) * (1 - a) * (1 - (ν : ℝ) ^ 2 / ((ν : ℝ) ^ 2 + J)) * t - ε * κ₁ * M ≤
            (cumArrivals tr (Sum.inl 0) t : ℝ) := by sorry

end MaxWeightInstab
