-- Prove2me | Theorems.Thm_IAFTRL_lemma_J_10
-- name    : IAFTRL.lemma_J_10
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T08:38:30.165752+00:00
-- url     : https://prove2.me/theorems/0f7b3f44-532c-4520-8554-2f1f3cc7e88b
-- title:
--   Lemma J.10 — exact compact-generator transfer
-- statement:
--   Let $\mathcal B\subseteq\mathcal A\subseteq\mathrm{Conv}(\mathcal B)$ be compact subsets of $\mathbb R^d$.
--
--   1. For every $z\in\mathbb R^d$,
--   $$
--   \sup_{a\in\mathcal A}|a^\top z|=\sup_{b\in\mathcal B}|b^\top z|.
--   $$
--   2. If $\theta$ has a unique optimal action $a^*\in\mathcal A$, then $c^*_{\mathrm{ctr}}(\mathcal A,\theta)=c^*_{\mathrm{ctr}}(\mathcal B,\theta)$.
--   3. Consider any run whose physical actions lie in $\mathcal B$, with measurable actions and loss vectors satisfying $\|\theta_t\|_{\mathcal A}\le1$. Then
--   $$
--   \sup_{a\in\mathcal A}\mathrm{Reg}_T(a)=\sup_{b\in\mathcal B}\mathrm{Reg}_T(b).
--   $$
--
--   So running on a generator loses nothing: the regret, the corruption norm and the information-acquisition complexity are the same whether they are measured on $\mathcal A$ or on $\mathcal B$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix J.2, Lemma J.10, p. 209

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Lemma J.10 (Exact compact-generator transfer).** Zhao–Tan, *Best-of-Both-Worlds FTRL for
Linear Bandits* (STOC submission version), Lemma J.10, p.209: "If known compact sets obey
`ℬ ⊆ 𝒜 ⊆ Conv(ℬ)`, then a strategy playing only `ℬ` satisfies
`sup_{a∈𝒜} Reg_T(a) = sup_{b∈ℬ} Reg_T(b)`, `sup_{a∈𝒜} |aᵀz| = sup_{b∈ℬ} |bᵀz|`.
For a unique optimal action `a*` under `θ`, `c*_ctr(𝒜, θ) = c*_ctr(ℬ, θ)`."

1. `‖z‖_𝒜 = ‖z‖_ℬ` for every `z`;
2. for a unique optimal action `a* ∈ 𝒜` under `θ`, `c*_ctr(𝒜, θ) = c*_ctr(ℬ, θ)`;
3. for every run whose physical actions lie in `ℬ` (measurable actions and loss vectors with
   `‖θ_t‖_𝒜 ≤ 1`), the suprema of the fixed-comparator regret over `𝒜` and over `ℬ` coincide. -/
theorem lemma_J_10 {d : ℕ} (𝒜 ℬ : Set (Fin d → ℝ)) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) :
    (∀ z : Fin d → ℝ, setNorm 𝒜 z = setNorm ℬ z) ∧
    (∀ θ astar : Fin d → ℝ, astar ∈ 𝒜 → (∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) →
      cstarCtr 𝒜 θ astar = cstarCtr ℬ θ astar) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
      (R : GRun d Ω), (∀ t < T, Measurable (R.A t) ∧ Measurable (R.θs t) ∧
        (∀ ω, R.A t ω ∈ ℬ) ∧ ∀ ω, setNorm 𝒜 (R.θs t ω) ≤ 1) →
      sSup (gRegretVs P T R '' 𝒜) = sSup (gRegretVs P T R '' ℬ)) := by sorry

end IAFTRL
