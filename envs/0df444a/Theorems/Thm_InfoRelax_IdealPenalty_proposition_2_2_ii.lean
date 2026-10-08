-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_proposition_2_2_ii
-- name    : InfoRelax.IdealPenalty.proposition_2_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:21.830588+00:00
-- url     : https://prove2.me/theorems/79c5fbad-502f-4b6c-9f45-409323bc770f
-- title:
--   Proposition 2.2(ii) — the penalty components are $\mathbb G$-adapted and nonanticipative in the actions
-- statement:
--   Let $\mathbb G$ be a relaxation of $\mathbb F$ and let $(w_0,\dots,w_T)$ be generating functions as in Proposition 2.2(i): each $w_t$ depends only on the first $t+1$ actions, is almost everywhere strongly measurable, and the family is bounded almost everywhere by one constant. Let $z_t(a)=\mathbb E[w_t(a)\mid\mathcal G_t]-\mathbb E[w_t(a)\mid\mathcal F_t]$. Then
--   1. for every action sequence $a$, the sequence $(z_0(a),\dots,z_T(a))$ is adapted to $\mathbb G$;
--   2. each $z_t$ depends only on the first $t+1$ actions $(a_0,\dots,a_t)$ of $a$.
--
--   Consequently the penalized objective decomposes into period-$t$ terms $r_t-z_t$ that depend only on what is known at time $t$ under $\mathbb G$ and the actions chosen up to $t$, which is what allows the dual problem to be solved by the recursion (10).
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, Proposition 2.2(ii)

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
import Definitions.Def_InfoRelax_IdealPenalty_Penalty

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **Proposition 2.2(ii) (Constructing Good Penalties)**, Brown, Smith & Sun (2010), Oper. Res.,
DOI 10.1287/opre.1090.0796, p. 5.

Let `𝔾` be a relaxation of `𝔽` and `(w_0, …, w_T)` generating functions, each `w_t` depending only
on `a_0, …, a_t`, and `z_t(a) = 𝔼[w_t(a) | 𝒢_t] − 𝔼[w_t(a) | 𝓕_t]`. Then `(z_0(a), …, z_T(a))` is
adapted to `𝔾` and `z_t` depends only on the first `t + 1` actions `(a_0, …, a_t)` of `a`.

**Formalization Note.** Same hypotheses as Proposition 2.2(i) (`GeneratingFns`); the countable
action type is not needed here and is not assumed. "Adapted" is Mathlib's `Adapted 𝔾` (each
`z_t(a)` is `𝒢_t`-measurable). The statement is close to definitional; it is the paper's
numbered result. -/
theorem proposition_2_2_ii {Ω X : Type*} [mΩ : MeasurableSpace Ω] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (h𝔾 : IsRelaxation 𝔽 𝔾) (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)
    (hw : GeneratingFns μ w) :
    (∀ a : Fin (T + 1) → X, Adapted 𝔾 (fun t => penaltyComp μ 𝔽 𝔾 w t a)) ∧
      ∀ (t : Fin (T + 1)) (a a' : Fin (T + 1) → X), (∀ s, s ≤ t → a s = a' s) →
        penaltyComp μ 𝔽 𝔾 w t a = penaltyComp μ 𝔽 𝔾 w t a' := by sorry

end InfoRelax.IdealPenalty
