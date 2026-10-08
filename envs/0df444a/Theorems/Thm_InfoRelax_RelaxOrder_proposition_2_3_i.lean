-- Prove2me | Theorems.Thm_InfoRelax_RelaxOrder_proposition_2_3_i
-- name    : InfoRelax.RelaxOrder.proposition_2_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:59.822253+00:00
-- url     : https://prove2.me/theorems/7ebbc711-6464-4e93-bfaa-51dc6ef50507
-- title:
--   Proposition 2.3(i) — with a common generating function, a looser relaxation gives a weaker dual bound
-- statement:
--   Consider a dynamic program in recursive form with countable action set: a natural filtration $\mathbb F$ with $\mathcal F_0=\{\emptyset,\Omega\}$, nonempty feasible-action sets $A_t(a_0,\dots,a_{t-1})$, and bounded $\mathcal F_t$-measurable period rewards $r_t(a_0,\dots,a_t)$, with total reward $r=\sum_t r_t$. Let $\mathbb G^1$ and $\mathbb G^2$ be filtrations with
--   $$\mathbb F\subseteq\mathbb G^1\subseteq\mathbb G^2,$$
--   let $(w_0,\dots,w_T)$ be one sequence of regular generating functions, and let $z^1,z^2$ be the penalties constructed by Proposition 2.2 with relaxations $\mathbb G^1,\mathbb G^2$ and these common generating functions:
--   $$z^i(a)=\sum_{t=0}^T\Big(\mathbb E[w_t(a)\mid\mathcal G^i_t]-\mathbb E[w_t(a)\mid\mathcal F_t]\Big),\qquad i=1,2.$$
--   Then
--   $$\sup_{\alpha_G\in\mathcal A_{\mathbb G^1}}\mathbb E\big[r(\alpha_G)-z^1(\alpha_G)\big]\le\sup_{\alpha_G\in\mathcal A_{\mathbb G^2}}\mathbb E\big[r(\alpha_G)-z^2(\alpha_G)\big].\qquad(12)$$
--
--   If penalties are generated with a common set of generating functions, looser relaxations lead to weaker upper bounds on the primal value. A simple generating function (say $w_t=0$) may thus give a good enough bound with one information relaxation but not with a looser one.
--
--   **Formalization Note** $z^1$ and $z^2$ are the penalties computed from $w$ by the formula of Proposition 2.2, not arbitrary penalties with its properties. Suprema are in the extended reals. A countable action set, bounded period rewards, and generating functions that are almost everywhere strongly measurable and uniformly bounded are pinned regularity assumptions of the recursive setting.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 6, Proposition 2.3(i), eq. (12)

import Mathlib
import Definitions.Def_InfoRelax_RelaxOrder_Framework
import Definitions.Def_InfoRelax_RelaxOrder_RecursiveModel
import Definitions.Def_InfoRelax_RelaxOrder_Penalty

open MeasureTheory

namespace InfoRelax.RelaxOrder

/-- **Proposition 2.3(i) (Properties of Penalties and Relaxations)**, Brown, Smith & Sun (2010),
Oper. Res., DOI 10.1287/opre.1090.0796, p. 6, eq. (12).

In the recursive setting, let `𝔾¹` and `𝔾²` be filtrations with `𝔽 ⊆ 𝔾¹ ⊆ 𝔾²`, and let `z¹`, `z²`
be the penalties constructed by Proposition 2.2 with relaxations `𝔾¹`, `𝔾²` and one common
sequence of generating functions `(w_0, …, w_T)`, i.e. `z^i(a) = ∑_t (𝔼[w_t(a) | 𝒢^i_t] − 𝔼[w_t(a) | 𝓕_t])`.
Then
`sup_{α_G ∈ 𝒜_{𝔾¹}} 𝔼[r(α_G) − z¹(α_G)] ≤ sup_{α_G ∈ 𝒜_{𝔾²}} 𝔼[r(α_G) − z²(α_G)]`:
with a common generating function, the looser relaxation gives the weaker (larger) bound.

**Formalization Note.** `z^i` is the `def` `penalty μ M.𝔽 𝔾^i w`, not an arbitrary penalty. The
bounds are suprema in `EReal` over the adapted policy sets. Pinned regularity of the recursive
setting: countable action type with the discrete σ-algebra, period rewards bounded
(`RecursiveDP.Valid`), generating functions a.e. strongly measurable and a.e. bounded by one
constant (`GeneratingFns`). -/
theorem proposition_2_3_i {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T) (hM : M.Valid)
    (𝔾₁ 𝔾₂ : Filtration (Fin (T + 1)) mΩ) (h₁ : InfoRelax.IdealPenalty.IsRelaxation M.𝔽 𝔾₁)
    (h₁₂ : InfoRelax.IdealPenalty.IsRelaxation 𝔾₁ 𝔾₂)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (hw : GeneratingFns μ w) :
    InfoRelax.IdealPenalty.dualBound μ M.A 𝔾₁ M.r (penalty μ M.𝔽 𝔾₁ w) ≤
      InfoRelax.IdealPenalty.dualBound μ M.A 𝔾₂ M.r (penalty μ M.𝔽 𝔾₂ w) := by sorry

end InfoRelax.RelaxOrder
