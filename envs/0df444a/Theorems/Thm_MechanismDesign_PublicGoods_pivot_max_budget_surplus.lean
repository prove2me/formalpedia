-- Prove2me | Theorems.Thm_MechanismDesign_PublicGoods_pivot_max_budget_surplus
-- name    : MechanismDesign.PublicGoods.pivot_max_budget_surplus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:19:52.724943+00:00
-- url     : https://prove2.me/theorems/5b86ecbe-eda4-41a3-b0b1-ecd48296cc7e
-- title:
--   Lemma 3.7 — the pivot mechanism has the largest expected budget surplus among IC, IR mechanisms implementing q*
-- statement:
--   In the public goods model of Börgers §3.3, the ex ante expected budget surplus of a direct mechanism $(q, t_1, \dots, t_N)$ is revenue minus cost,
--   $$\int_\Theta \Big(\sum_{i\in I} t_i(\theta) - c\,q(\theta)\Big) f(\theta)\,d\theta .$$
--
--   **Lemma 3.7.** No incentive-compatible and individually rational direct mechanism that implements the first best decision rule $q^*$ has a larger ex ante expected budget surplus than the pivot mechanism.
--
--   Together with Lemma 3.8 this shows that, in the nontrivial case, every incentive-compatible and individually rational mechanism implementing $q^*$ runs an expected deficit, which is the core of Proposition 3.7.
--
--   **Formalization Note** "Implements $q^*$" is read as $q(\theta) = q^*(\theta)$ for every $\theta\in\Theta$. The competing mechanism belongs to the class `IsDirect` (measurability and integrability made explicit).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.52, Lemma 3.7

import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Lemma 3.7 (p.52): no incentive-compatible and individually rational direct mechanism
that implements the first best decision rule `q*` has a larger ex ante expected budget surplus
(revenue minus cost) than the pivot mechanism. -/
theorem pivot_max_budget_surplus {N : ℕ} (S : Setting N) (M : DirectMechanism N)
    (hM : M.IsDirect S) (hIC : M.IsIC S) (hIR : M.IsIR S)
    (hq : ∀ θ ∈ S.typeSpace, M.q θ = S.qStar θ) :
    M.budgetSurplus S ≤ S.pivot.budgetSurplus S := by sorry

end MechanismDesign.PublicGoods
