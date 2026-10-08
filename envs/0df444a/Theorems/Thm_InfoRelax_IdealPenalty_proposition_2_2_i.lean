-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_proposition_2_2_i
-- name    : InfoRelax.IdealPenalty.proposition_2_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:14.858068+00:00
-- url     : https://prove2.me/theorems/71b24159-1102-4539-9e51-f9b2e7c4138c
-- title:
--   Proposition 2.2(i) — penalties from generating functions have zero conditional mean under $\mathbb F$
-- statement:
--   Let $\mathbb G$ be a relaxation of $\mathbb F$, let the action set be countable, and let $(w_0,\dots,w_T)$ be generating functions such that each $w_t$ depends only on the first $t+1$ actions, each $w_t(a)$ is almost everywhere strongly measurable, and all are bounded almost everywhere by one constant. Define
--   $$z_t(a)=\mathbb E[w_t(a)\mid\mathcal G_t]-\mathbb E[w_t(a)\mid\mathcal F_t],\qquad z(a)=\sum_{t=0}^T z_t(a).$$
--   Then $\mathbb E[z(\alpha)]$ exists for every policy $\alpha$ (so $z\in\mathcal Z$), and for every nonanticipative policy $\alpha_F\in\mathcal A_{\mathbb F}$,
--   $$\mathbb E[z_t(\alpha_F)\mid\mathcal F_t]=0\ \text{ almost surely, for all } t,\qquad\text{and}\qquad\mathbb E[z(\alpha_F)]=0.$$
--
--   In particular $z$ is dual feasible, with the defining inequality of $\mathcal Z_{\mathbb F}$ holding with equality.
--
--   **Formalization Note** $z_t(\alpha_F)$ is the random variable $\omega\mapsto z_t(\alpha_F(\omega))(\omega)$, where each $z_t(a)$ is a fixed version of a conditional expectation. The countable action set and the almost-everywhere bound are pinned regularity assumptions.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, Proposition 2.2(i)

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
import Definitions.Def_InfoRelax_IdealPenalty_Penalty

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **Proposition 2.2(i) (Constructing Good Penalties)**, Brown, Smith & Sun (2010), Oper. Res.,
DOI 10.1287/opre.1090.0796, p. 5.

Let `𝔾` be a relaxation of `𝔽` and `(w_0, …, w_T)` generating functions, each `w_t` depending only
on `a_0, …, a_t`. Put `z_t(a) = 𝔼[w_t(a) | 𝒢_t] − 𝔼[w_t(a) | 𝓕_t]` and `z(a) = ∑_t z_t(a)`. Then
for all `α_F ∈ 𝒜_𝔽`, `𝔼[z_t(α_F) | 𝓕_t] = 0` for all `t`, and `𝔼[z(α_F)] = 0`.

The first conjunct, `z ∈ 𝒵` (the expectations `𝔼[z(α)]` exist for every policy), is part of
the statement so that (i) yields `z ∈ 𝒵_𝔽`.

**Formalization Note.** `z_t(α_F)` is the random variable `ω ↦ z_t(α_F(ω))(ω)`, where each
`z_t(a)` is a fixed version of a conditional expectation. Pinned regularity: countable action type
with the discrete σ-algebra; the `w_t(a)` a.e. strongly measurable and a.e. bounded by one constant
(`GeneratingFns`). `𝔼[· | 𝓕_t] = 0` holds almost surely. -/
theorem proposition_2_2_i {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set (Fin (T + 1) → X)) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (h𝔾 : IsRelaxation 𝔽 𝔾) (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)
    (hw : GeneratingFns μ w) :
    penalty μ 𝔽 𝔾 w ∈ penalties μ A ∧
      ∀ α ∈ adaptedPolicies A 𝔽,
        (∀ t, μ[fun ω => penaltyComp μ 𝔽 𝔾 w t (α ω) ω | 𝔽 t] =ᵐ[μ] 0) ∧
          ∫ ω, penalty μ 𝔽 𝔾 w (α ω) ω ∂μ = 0 := by sorry

end InfoRelax.IdealPenalty
