-- Prove2me | Theorems.Thm_MechanismDesign_PublicGoods_exAnte_budget_balance_to_exPost
-- name    : MechanismDesign.PublicGoods.exAnte_budget_balance_to_exPost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:19:41.412539+00:00
-- url     : https://prove2.me/theorems/3c23d880-7fbc-4112-b593-8aa4f077a437
-- title:
--   Proposition 3.6 — ex ante budget balance can be turned into ex post budget balance
-- statement:
--   Consider the public goods model of Börgers §3.3: $N \ge 2$ agents with independent types $\theta_i$ on $[\underline\theta,\bar\theta]$ with positive densities $f_i$, and cost $c > 0$. A direct mechanism $(q, t_1, \dots, t_N)$ is ex ante budget balanced if
--   $$\int_\Theta \sum_{i\in I} t_i(\theta) f(\theta)\,d\theta \;\ge\; \int_\Theta c\,q(\theta) f(\theta)\,d\theta,$$
--   and ex post budget balanced if $\sum_{i\in I} t_i(\theta) \ge c\,q(\theta)$ for every $\theta\in\Theta$.
--
--   **Proposition 3.6.** For every direct mechanism that is ex ante budget balanced, there is an equivalent direct mechanism that is ex post budget balanced. Here "equivalent" (Definition 3.7) means: the same decision rule, and for every agent $i$ and every report $\theta_i'$, the same expected transfer of agent $i$ conditional on her report $\theta_i'$.
--
--   Since equivalent mechanisms share incentive compatibility and individual rationality, the result shows that the ex post and the ex ante budget constraints describe the same set of implementable outcomes, so later results may use whichever is more convenient.
--
--   **Formalization Note** Both mechanisms range over the class `IsDirect`, which adds the measurability and integrability the book leaves implicit; the constructed mechanism must belong to the same class.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.48, Proposition 3.6

import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Proposition 3.6 (p.48): for every direct mechanism that is ex ante budget balanced
(Definition 3.6) there is an equivalent (Definition 3.7) direct mechanism that is ex post budget
balanced (Definition 3.5). -/
theorem exAnte_budget_balance_to_exPost {N : ℕ} (S : Setting N) (M : DirectMechanism N)
    (hM : M.IsDirect S) (hBB : M.IsExAnteBB S) :
    ∃ M' : DirectMechanism N, M'.IsDirect S ∧ M.Equivalent S M' ∧ M'.IsExPostBB S := by sorry

end MechanismDesign.PublicGoods
