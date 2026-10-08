-- Prove2me | Theorems.Thm_InfoRelax_RelaxOrder_proposition_2_3_iii
-- name    : InfoRelax.RelaxOrder.proposition_2_3_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:53.541056+00:00
-- url     : https://prove2.me/theorems/ffee7586-46d0-4879-a35d-f468c5bf2950
-- title:
--   Proposition 2.3(iii) — penalties built with an intermediate filtration $\mathbb F'$ are good penalties
-- statement:
--   Let $\mathbb F'$ and $\mathbb G$ be filtrations with $\mathbb F\subseteq\mathbb F'\subseteq\mathbb G$, let the action set be countable, and let $(w_0,\dots,w_T)$ be regular generating functions, each $w_t$ depending only on the first $t+1$ actions. Define
--   $$z_t(a)=\mathbb E[w_t(a)\mid\mathcal G_t]-\mathbb E[w_t(a)\mid\mathcal F'_t],\qquad z(a)=\sum_{t=0}^T z_t(a).$$
--   Then $z$ satisfies the results of Proposition 2.2, which reads (p. 5):
--
--   > Let $\mathbb G$ be a relaxation of $\mathbb F$ and let $(w_0(a,\omega),\dots,w_T(a,\omega))$ be a sequence of generating functions defined on $A\times\Omega$ where each $w_t$ depends only on the first $t+1$ actions $(a_0,\dots,a_t)$ of $a$. Define $z_t(a)=\mathbb E[w_t(a)\mid\mathcal G_t]-\mathbb E[w_t(a)\mid\mathcal F_t]$ and $z(a)=\sum_{t=0}^T z_t(a)$. Then: (i) For all $\alpha_F$ in $\mathcal A_{\mathbb F}$, we have $\mathbb E[z_t(\alpha_F)\mid\mathcal F_t]=0$ for all $t$, and $\mathbb E[z(\alpha_F)]=0$; and (ii) $(z_0(a),\dots,z_T(a))$ is adapted to $\mathbb G$ and $z_t$ depends only on the first $t+1$ actions $(a_0,\dots,a_t)$ of $a$.
--
--   That is:
--   1. $\mathbb E[z(\alpha)]$ exists for every policy $\alpha$, and for every nonanticipative $\alpha_F\in\mathcal A_{\mathbb F}$, $\mathbb E[z_t(\alpha_F)\mid\mathcal F_t]=0$ almost surely for all $t$, and $\mathbb E[z(\alpha_F)]=0$;
--   2. for every $a$, $(z_0(a),\dots,z_T(a))$ is adapted to $\mathbb G$, and $z_t$ depends only on $a_0,\dots,a_t$.
--
--   In particular $z$ is dual feasible. The result allows the subtracted conditional expectation to be computed under more information than the natural filtration, when $\mathbb E[w_t(a)\mid\mathcal F_t]$ is hard to compute.
--
--   **Formalization Note** $z_t(\alpha_F)$ is the random variable $\omega\mapsto z_t(\alpha_F(\omega))(\omega)$. The first clause of item 1 is added so that item 1 yields $z\in\mathcal Z_{\mathbb F}$. Proposition 2.2 itself is the case $\mathbb F'=\mathbb F$.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 6, Proposition 2.3(iii) (with Proposition 2.2, p. 5)

import Mathlib
import Definitions.Def_InfoRelax_RelaxOrder_Framework
import Definitions.Def_InfoRelax_RelaxOrder_RecursiveModel
import Definitions.Def_InfoRelax_RelaxOrder_Penalty

open MeasureTheory

namespace InfoRelax.RelaxOrder

/-- **Proposition 2.3(iii)**, Brown, Smith & Sun (2010), Oper. Res., DOI 10.1287/opre.1090.0796,
p. 6.

Let `𝔽′` and `𝔾` be filtrations with `𝔽 ⊆ 𝔽′ ⊆ 𝔾` and `(w_0, …, w_T)` generating functions as in
Proposition 2.2. The penalty `z_t(a) = 𝔼[w_t(a) | 𝒢_t] − 𝔼[w_t(a) | 𝓕′_t]`, `z(a) = ∑_t z_t(a)`,
satisfies the results of Proposition 2.2 (p. 5), with the original `𝔽` and `𝔾`:
1. `z ∈ 𝒵` (its expectation exists along every policy) and, for every `α_F ∈ 𝒜_𝔽`,
   `𝔼[z_t(α_F) | 𝓕_t] = 0` almost surely for all `t`, and `𝔼[z(α_F)] = 0` (Prop. 2.2(i));
2. `(z_0(a), …, z_T(a))` is adapted to `𝔾` for every `a`, and `z_t` depends only on the first
   `t + 1` actions `a_0, …, a_t` (Prop. 2.2(ii)).

**Formalization Note.** `z_t(α_F)` is the random variable `ω ↦ z_t(α_F(ω))(ω)`, each `z_t(a)` a
fixed version of a difference of conditional expectations. The conjunct `z ∈ 𝒵` makes (i) yield
`z ∈ 𝒵_𝔽`. Pinned regularity: countable action type with the discrete σ-algebra; generating
functions as in `GeneratingFns`. Proposition 2.2 itself is the case `𝔽′ = 𝔽`. -/
theorem proposition_2_3_iii {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set (Fin (T + 1) → X)) (𝔽 𝔽' 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (h𝔽' : InfoRelax.IdealPenalty.IsRelaxation 𝔽 𝔽') (h𝔾 : InfoRelax.IdealPenalty.IsRelaxation 𝔽' 𝔾)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (hw : GeneratingFns μ w) :
    (penalty μ 𝔽' 𝔾 w ∈ InfoRelax.IdealPenalty.penalties μ A ∧
      ∀ α ∈ InfoRelax.IdealPenalty.adaptedPolicies A 𝔽,
        (∀ t, μ[fun ω => penaltyComp μ 𝔽' 𝔾 w t (α ω) ω | 𝔽 t] =ᵐ[μ] 0) ∧
          ∫ ω, penalty μ 𝔽' 𝔾 w (α ω) ω ∂μ = 0) ∧
    ((∀ a : Fin (T + 1) → X, Adapted 𝔾 (fun t => penaltyComp μ 𝔽' 𝔾 w t a)) ∧
      ∀ (t : Fin (T + 1)) (a a' : Fin (T + 1) → X), (∀ s, s ≤ t → a s = a' s) →
        penaltyComp μ 𝔽' 𝔾 w t a = penaltyComp μ 𝔽' 𝔾 w t a') := by sorry

end InfoRelax.RelaxOrder
