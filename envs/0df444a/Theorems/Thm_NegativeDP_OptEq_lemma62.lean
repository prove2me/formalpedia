-- Prove2me | Theorems.Thm_NegativeDP_OptEq_lemma62
-- name    : NegativeDP.OptEq.lemma62
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:57.811983+00:00
-- url     : https://prove2.me/theorems/057e0ba3-ee81-45fc-9b5f-bafce71fca79
-- title:
--   Lemma 6.2 (N) — $U$ conserves $v'_\pi = \sup_n I({}^n\pi)$ and $v_\pi = \lim_n U^n v'_\pi$
-- statement:
--   Let $\hat\pi$ be a Markov policy of a negative dynamic programming problem with operator $U$, and let $\pi = (f_1,f_2,\dots)\in G(\hat\pi)$. Writing ${}^n\pi = (f_{n+1},f_{n+2},\dots)$, define
--   $$v'_\pi = \sup_{n\ge 0} I({}^n\pi), \qquad v_\pi = \lim_{n\to\infty} U^n v'_\pi .$$
--   Then $U$ conserves $v'_\pi$ (that is, $v'_\pi\in M(S)$ and $Uv'_\pi \ge v'_\pi$), the limit defining $v_\pi$ exists at every state, and $U$ conserves $v_\pi$.
--
--   These conserved functions dominate the return of every policy in $G(\hat\pi)$; combined with Theorem 6.1 they produce Markov policies improving on a given sequence of Markov policies (Theorem 6.2).
--
--   The paper states this for the discounted (previously known) and negative cases; this item is the negative case. **Formalization Note** The paper defines $v_\pi$ as a limit; the statement asserts the pointwise existence of the limit $w$ of $U^n v'_\pi$ (in `EReal`) and that $U$ conserves $w$. `Conserves` includes membership in $M(S)$, so the measurability of $v'_\pi$ and $v_\pi$, which the paper takes for granted, is part of the conclusion. $U^n$ is the $n$-fold iterate of $U$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 882, Lemma 6.2 (with the definitions of v'_π and v_π preceding it)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.OptEq

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Strauch (1966), Lemma 6.2, p. 882, negative case. For `π ∈ G(π̂)` let
`v'_π = sup_{n ≥ 0} I(ⁿπ)`. Then `U` conserves `v'_π`, the limit `v_π = limₙ Uⁿ v'_π` exists
pointwise, and `U` conserves `v_π`. -/
theorem lemma62 (P : NegativeDP.Stationary.Problem S A) (πhat π : MarkovPlan S A) (hπ : IsGeneratedPlan πhat π)
    (v' : S → EReal) (hv' : ∀ s, v' s = ⨆ n : ℕ, NegativeDP.Stationary.I P (shift π n).toPlan s) :
    Conserves P πhat v' ∧
      ∃ w : S → EReal,
        (∀ s, Tendsto (fun n : ℕ => (U P πhat)^[n] v' s) atTop (𝓝 (w s))) ∧
        Conserves P πhat w := by sorry

end NegativeDP.OptEq
