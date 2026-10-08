-- Prove2me | Theorems.Thm_InfoRelax_RelaxOrder_proposition_2_3_iv
-- name    : InfoRelax.RelaxOrder.proposition_2_3_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:11.744771+00:00
-- url     : https://prove2.me/theorems/dc0aa611-c47c-4e35-8a39-87995305e8b8
-- title:
--   Proposition 2.3(iv) — unbiased estimated penalties give valid but weaker bounds
-- statement:
--   Let the action set be countable, let $\mathbb E[r(\alpha)]$ exist for every policy $\alpha$, and let $\mathbb G$ be a relaxation of $\mathbb F$. Let $z(a)=\sum_{t=0}^T z_t(a)$ be a dual feasible penalty such that each $z_t(a)$ is $\mathcal G_t$-measurable and depends only on the first $t+1$ actions of $a$. Let $\hat z(a)=\sum_{t=0}^T\hat z_t(a)$, where each $\hat z_t(a)$ is an $\mathcal F$-measurable, uniformly bounded random variable that depends only on the first $t+1$ actions of $a$ and is an **unbiased estimate** of $z_t(a)$:
--   $$\mathbb E[\hat z_t(a)\mid\mathcal G_t]=z_t(a)\quad\text{almost surely}.$$
--   Let $\widehat{\mathbb G}$ be the relaxation of $\mathbb G$ in which the values $\hat z_t(a)$ are revealed in period $t$, $\widehat{\mathcal G}_t=\mathcal G_t\vee\sigma(\hat z_s(a): s\le t,\ a)$. Then
--   $$\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E\big[r(\alpha_G)-z(\alpha_G)\big]\le\sup_{\alpha_G\in\mathcal A_{\widehat{\mathbb G}}}\mathbb E\big[r(\alpha_G)-\hat z(\alpha_G)\big].\qquad(14)$$
--
--   When penalties are estimated, for instance by nested simulation, and the estimates are unbiased, the resulting bounds remain valid upper bounds on the primal value, but they are weaker than the bounds given by the true penalty.
--
--   **Formalization Note** $\widehat{\mathbb G}$ is constructed from $\mathbb G$ and $\hat z$, not taken as an arbitrary filtration. The measurability and the uniform bound of the estimates are pinned regularity assumptions; the measurability is also what makes $\widehat{\mathbb G}$ a filtration of $\mathcal F$. Suprema are in the extended reals.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 6, Proposition 2.3(iv), eq. (14)

import Mathlib
import Definitions.Def_InfoRelax_RelaxOrder_Framework
import Definitions.Def_InfoRelax_RelaxOrder_RevealedFiltration

open MeasureTheory

namespace InfoRelax.RelaxOrder

/-- **Proposition 2.3(iv)**, Brown, Smith & Sun (2010), Oper. Res., DOI 10.1287/opre.1090.0796,
p. 6, eq. (14).

Let `𝔾` be a relaxation of `𝔽` and `z(a) = ∑_t z_t(a)` a dual feasible penalty such that each
`z_t(a)` is `𝒢_t`-measurable and depends only on the first `t + 1` actions of `a`. Let
`ẑ(a) = ∑_t ẑ_t(a)` where each `ẑ_t(a)` depends only on the first `t + 1` actions of `a` and is an
unbiased estimate of `z_t(a)`: `𝔼[ẑ_t(a) | 𝒢_t] = z_t(a)`. Let `𝔾̂` be the relaxation of `𝔾` in
which, in addition to what is known under `𝔾`, the values `ẑ_t(a)` are revealed in period `t`.
Then
`sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z(α_G)] ≤ sup_{α_G ∈ 𝒜_𝔾̂} 𝔼[r(α_G) − ẑ(α_G)]`.

**Formalization Note.** `zhat` is the page's `ẑ`; `𝔾̂` is the constructed filtration
`revealedFiltration 𝔾 zhat _`, `𝒢̂_t = 𝒢_t ∨ σ(ẑ_s(a) : s ≤ t, all a)`. General feasible set `A`
and total reward `r` (expectation existing along every policy). Unbiasedness holds almost surely
(conditional expectations are determined a.e.). Pinned regularity: countable action type with the
discrete σ-algebra; each `ẑ_t(a)` is `𝓕`-measurable (needed for `𝔾̂` to be a filtration of `𝓕`)
and the family is a.e. bounded by one constant. -/
theorem proposition_2_3_iv {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set (Fin (T + 1) → X)) (r : (Fin (T + 1) → X) → Ω → ℝ) (hr : InfoRelax.IdealPenalty.RewardIntegrable μ A r)
    (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ) (h𝔾 : InfoRelax.IdealPenalty.IsRelaxation 𝔽 𝔾)
    (zt : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)
    (hz : (fun a ω => ∑ t, zt t a ω) ∈ InfoRelax.IdealPenalty.dualFeasible μ A 𝔽)
    (hzt_meas : ∀ t a, Measurable[𝔾 t] (zt t a))
    (hzt_dep : ∀ t a a', (∀ s, s ≤ t → a s = a' s) → zt t a = zt t a')
    (zhat : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)
    (hzhat_meas : ∀ t a, Measurable (zhat t a))
    (hzhat_bdd : ∃ C : ℝ, ∀ t a, ∀ᵐ ω ∂μ, |zhat t a ω| ≤ C)
    (hzhat_dep : ∀ t a a', (∀ s, s ≤ t → a s = a' s) → zhat t a = zhat t a')
    (hunbiased : ∀ t a, μ[zhat t a | 𝔾 t] =ᵐ[μ] zt t a) :
    InfoRelax.IdealPenalty.dualBound μ A 𝔾 r (fun a ω => ∑ t, zt t a ω) ≤
      InfoRelax.IdealPenalty.dualBound μ A (revealedFiltration 𝔾 zhat hzhat_meas) r
        (fun a ω => ∑ t, zhat t a ω) := by sorry

end InfoRelax.RelaxOrder
