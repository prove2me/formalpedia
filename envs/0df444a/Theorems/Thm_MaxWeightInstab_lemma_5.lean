-- Prove2me | Theorems.Thm_MaxWeightInstab_lemma_5
-- name    : MaxWeightInstab.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:13.783998+00:00
-- url     : https://prove2.me/theorems/7c45e033-2354-4e46-99e8-229948831aab
-- title:
--   Lemma 5 — the queues $\mathcal A_1,\dots,\mathcal A_J$ stay balanced up to time $T$
-- statement:
--   Let $\gamma$ satisfy (11) and assume the initial condition (13). On the event $G_M$,
--
--   $$
--   \max_{j,j'=1,\dots,J}\ \max_{0\le t\le T}\ \big|Q_{\mathcal A_j}(t)-Q_{\mathcal A_{j'}}(t)\big|\ \le\ \frac{\varepsilon M}{\nu}+3\varepsilon bT .
--   $$
--
--   MaxWeight serves only the longest of the queues $\mathcal A_1,\dots,\mathcal A_J$, so their differences are controlled by the differences of their arrival counts.
--
--   **Formalization Note** For every $\varepsilon>0$ there is $M_0$ (the proof ends "for large $T$", and $T$ is proportional to $M$) such that the bound holds for every $M\ge M_0$, every MaxWeight trajectory with $Q(0)\in\mathcal I_M$, every arrival path in $G_M$ and every integer $t\le T$.
--
--   Differences from the source:
--   - generalization: ε ∈ (0, ε₀), the section's standing choice (p.6) → every ε > 0; reason: the lemma does not depend on ε being small; specializes to the source
--   - reading: "for large T" at the end of the proof → a threshold M₀ for each ε; reason: T is proportional to M
--   - encoding: "on the event G_M" for the random queue process → every MaxWeight trajectory (any tie choices) whose arrival path satisfies (15); reason: the statement is pathwise and G_M constrains the arrivals only; same content
--   - reading: γ: the section's standing choice satisfying (11) (pp.6–7), not restated in the lemma → hypothesis 1 < γ < a/(1 − a + aν/J); reason: γ enters G_M through b; standing assumption of §3.1
--   - encoding: J ∈ ℤ₊, ν ∈ ℕ with 1/ν in (3)–(4) → 0 < J and 0 < ν; reason: excludes only the cases where a/J or 1/ν is undefined
--   - reading: sup over 0 ≤ s ≤ t ≤ T in G_M (15), and the times t of the conclusion → integer times; reason: the process is indexed by t ∈ ℤ₊ (p.1, p.5) and (19) sums over t = 0, …, T
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Lemma 5, p.11

import Mathlib
import Definitions.Def_MaxWeightInstab_IsInitial
import Definitions.Def_MaxWeightInstab_IsGoodArrivals
import Definitions.Def_MaxWeightInstab_Trajectory

namespace MaxWeightInstab

/-- **Lemma 5** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.11). Assume (13). On the event `G_M`,
`max_{j,j′=1,…,J} max_{0≤t≤T} |Q_{𝒜_j}(t) − Q_{𝒜_{j′}}(t)| ≤ εM/ν + 3εbT`.

**Formalization Note.** The lemma assumes only (13); `γ` with (11) is the section's standing choice
(it enters `G_M` and the bound through `b`), and `J, ν ≥ 1`. Its proof ends "for large T", so for
each `ε > 0` there is a threshold `M₀` (`T` is proportional to `M`). The statement is made for every
`ε > 0` rather than `ε ∈ (0, ε₀)`, and every MaxWeight trajectory (any tie choices). Times are
integers `0 ≤ t ≤ T`. -/
theorem lemma_5 (J ν : ℕ) (a γ : ℝ) (hJ : 0 < J) (hν : 0 < ν)
    (h11 : 1 < γ ∧ γ < a / (1 - a + a * ν / J)) :
    ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
      ∀ tr : Trajectory J ν, IsInitial ν ε M (tr.Q 0) → IsGoodArrivals a J ν γ ε M tr.e →
        ∀ j j' : Fin J, ∀ t : ℕ, (t : ℝ) ≤ horizon a ν M →
          |(tr.Q t (Sum.inl j.succ) : ℝ) - tr.Q t (Sum.inl j'.succ)| ≤
            ε * M / ν + 3 * ε * bConst a J ν γ * horizon a ν M := by sorry

end MaxWeightInstab
