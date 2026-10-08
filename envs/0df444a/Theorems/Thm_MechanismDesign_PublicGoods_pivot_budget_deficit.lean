-- Prove2me | Theorems.Thm_MechanismDesign_PublicGoods_pivot_budget_deficit
-- name    : MechanismDesign.PublicGoods.pivot_budget_deficit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:20:04.061099+00:00
-- url     : https://prove2.me/theorems/503875e6-eb8b-4763-967f-97cd7d58cb50
-- title:
--   Lemma 3.8 — the pivot mechanism runs an expected deficit when $N\underline\theta < c < N\bar\theta$
-- statement:
--   In the public goods model of Börgers §3.3 (types on $[\underline\theta,\bar\theta]$, cost $c>0$, $N \ge 2$ agents), consider the pivot mechanism of Definition 3.8.
--
--   **Lemma 3.8.** If $N\underline\theta < c < N\bar\theta$, then the ex ante expected budget surplus of the pivot mechanism is negative:
--   $$\int_\Theta \Big(\sum_{i\in I} t_i(\theta) - c\,q^*(\theta)\Big) f(\theta)\,d\theta < 0 .$$
--
--   The condition excludes exactly the two trivial cases in which production is efficient for every type vector or for none. Combined with Lemma 3.7, it rules out an incentive-compatible, individually rational first best mechanism.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.53, Lemma 3.8

import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Lemma 3.8 (p.53): if `N θ̲ < c < N θ̄`, then the ex ante expected budget surplus of
the pivot mechanism is negative. -/
theorem pivot_budget_deficit {N : ℕ} (S : Setting N)
    (hlow : (N : ℝ) * S.θlo < S.c) (hhigh : S.c < (N : ℝ) * S.θhi) :
    S.pivot.budgetSurplus S < 0 := by sorry

end MechanismDesign.PublicGoods
