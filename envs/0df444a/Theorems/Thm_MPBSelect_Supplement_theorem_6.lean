-- Prove2me | Theorems.Thm_MPBSelect_Supplement_theorem_6
-- name    : MPBSelect.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:50:12.366797+00:00
-- url     : https://prove2.me/theorems/d80f4784-9342-5dec-b0a3-045e4f4b572a
-- title:
--   Theorem 6 — iff optimality systems for the favorable-set OCBA problems
-- statement:
--   Let $\boldsymbol\alpha$ be feasible. It is optimal for the favorable-set accuracy problem (28) if and only if it satisfies the full global balance at every parameter and $W^{\mathrm{ACC}}$ pairwise balance on $\Xi\cup\Xi^{\mathrm{adv}}$. Simultaneously, it is optimal for the false-negative problem (29) if and only if it satisfies the same global balance and $W^{\mathrm{FN}}$ pairwise balance on that set.
--
--   In the global equation the sum contains every $i\ne i^b$, including $i^*$; neither characterization has a zero-ratio clause.
--
--   Differences from the source:
--   - encoding: the two “respectively” iff statements in one paragraph → a conjunction of the complete iff for (28) and the complete iff for (29); reason: both clauses of the printed theorem are retained
--   - encoding: weights are $+\infty$ outside $\Xi\cup\Xi^{\mathrm{adv}}$ → the objectives and pairwise equations are restricted to that active nonempty set; reason: the same finite minima and equations result
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 6 and (30), p.26

import Mathlib
import Definitions.Def_MPBSelect_Supplement_Favorable

namespace MPBSelect.Supplement

/-- **Theorem 6 (optimality conditions for (28) and (29)).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 6,
p.26, equation (30).

For every feasible allocation, optimality for the favorable-set accuracy problem and for the
false-negative problem is characterized, respectively, by the full global balance and the
`W^ACC` or `W^FN` pairwise balance on `Ξ ∪ Ξ^adv`. -/
theorem theorem_6 {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) (hα : α ∈ MPBSelect.feasibleSet k B) :
    (IsOptimalAcc P α ↔ GlobalBalanceAll P α ∧ PairwiseBalanceAcc P α) ∧
    (IsOptimalFN P α ↔ GlobalBalanceAll P α ∧ PairwiseBalanceFN P α) := by sorry

end MPBSelect.Supplement
