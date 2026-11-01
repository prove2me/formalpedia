-- Prove2me | Theorems.Thm_MaxWeightInstab_lemma_2
-- name    : MaxWeightInstab.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:23.24503+00:00
-- url     : https://prove2.me/theorems/7dddb77d-af82-4e39-bd46-6827de0cf4c1
-- title:
--   Lemma 2 — component $\mathcal B$ is almost empty by time $U\le 2M/(1-r_{\boldsymbol\rho})<T$
-- statement:
--   Assume (4), let $\gamma$ satisfy (11), and assume the initial condition (13) with $M$ satisfying (12). Then on the event $G_M$,
--
--   $$
--   U\ \le\ \frac{2M}{1-a(1+1/\nu)} . \tag{22}
--   $$
--
--   In particular, $U<T$.
--
--   Here $U$ is the first time at which component $\mathcal B$ holds at most $\nu^2$ jobs, (21). The lemma says that the initial $M$ jobs at $\mathcal B$ are cleared well before the horizon $T$ of (14), since component $\mathcal B$ is subcritical.
--
--   **Formalization Note** There are $\varepsilon_0,L>0$ depending only on $a,J,\nu,\gamma$ such that for every $\varepsilon\in(0,\varepsilon_0)$ there is $M_0$ with the conclusion for every $M\ge\max(L/\varepsilon,M_0)$, every MaxWeight trajectory with $Q(0)\in\mathcal I_M$ and every arrival path in $G_M$.
--
--   Differences from the source:
--   - reading: ε ∈ (0, ε₀) and M ≥ L/ε (12) with ε₀, L depending only on a, J, ν, γ (p.6), M large enough that T ≥ C (p.7) and the proofs' "for large M" → ∃ ε₀, L > 0, ∀ ε ∈ (0, ε₀), ∃ M₀, ∀ M ≥ max(L/ε, M₀); reason: the quantifier order of pp.6–7; the per-ε threshold M₀ collects "T ≥ C" and the in-proof "for large M"
--   - encoding: "on the event G_M" for the random queue process → every MaxWeight trajectory (any tie choices) whose arrival path satisfies (15); reason: the statement is pathwise and G_M constrains the arrivals only; same content
--   - encoding: U, V := min{…} ∧ T (21) → first integer time at which the condition holds or t ≥ T (so ⌈T⌉ instead of T when the condition never holds before T); reason: Q(U), Q(V) must be defined; the two agree whenever the condition occurs before T, which (22) and Lemma 7 assert
--   - reading: γ: the section's standing choice satisfying (11) (pp.6–7), not restated in the lemma → hypothesis 1 < γ < a/(1 − a + aν/J); reason: γ enters G_M through b; standing assumption of §3.1
--   - encoding: J ∈ ℤ₊, ν ∈ ℕ with 1/ν in (3)–(4) → 0 < J and 0 < ν; reason: excludes only the cases where a/J or 1/ν is undefined
--   - reading: sup over 0 ≤ s ≤ t ≤ T in G_M (15), and the times t of the conclusion → integer times; reason: the process is indexed by t ∈ ℤ₊ (p.1, p.5) and (19) sums over t = 0, …, T
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Lemma 2, p.9

import Mathlib
import Definitions.Def_MaxWeightInstab_IsInitial
import Definitions.Def_MaxWeightInstab_IsGoodArrivals
import Definitions.Def_MaxWeightInstab_hitU

namespace MaxWeightInstab

/-- **Lemma 2** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.9). Assume (4), and assume (13) with `M` satisfying (12). On the
event `G_M`, `U ≤ 2M/(1 − a(1 + 1/ν))` (22). In particular, `U < T`.

**Formalization Note.** Quantifiers as on pp.6–7: the constants `ε₀`, `L` depend only on
`a, J, ν, γ` ("the constants ϵ₀, L, κ₁, ..., κ₄ will depend only on the parameters a, J, ν, and γ",
p.6); for each `ε ∈ (0, ε₀)` a threshold `M₀` collects "assume M to be sufficiently large so that
T ≥ C" (p.7) and the proofs' "for large M"; then the claim holds for every `M ≥ max(L/ε, M₀)` (12),
every MaxWeight trajectory (any tie choices) with `Q(0)` satisfying (13), and every arrival path in
`G_M` (15). `U`, `V` are the integer stopping times of (21) (`hitU`, `hitV`). The section's `γ` with (11) is assumed (it enters `G_M` through `b`);
`J, ν ≥ 1` are the network's standing nondegeneracy. -/
theorem lemma_2 (J ν : ℕ) (a γ : ℝ) (hJ : 0 < J) (hν : 0 < ν) (h4 : rRho a ν < 1)
    (h11 : 1 < γ ∧ γ < a / (1 - a + a * ν / J)) :
    ∃ ε₀ > 0, ∃ L > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → L / ε ≤ M →
      ∀ tr : Trajectory J ν, IsInitial ν ε M (tr.Q 0) → IsGoodArrivals a J ν γ ε M tr.e →
        (hitU tr (horizon a ν M) : ℝ) ≤ 2 * M / (1 - a * (1 + 1 / (ν : ℝ))) ∧
        (hitU tr (horizon a ν M) : ℝ) < horizon a ν M := by sorry

end MaxWeightInstab
