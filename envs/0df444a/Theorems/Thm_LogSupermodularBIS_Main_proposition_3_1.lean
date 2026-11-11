-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_proposition_3_1
-- name    : LogSupermodularBIS.Main.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:50.459182+00:00
-- url     : https://prove2.me/theorems/e38908d9-c48b-402e-80f4-49beed546c4b
-- title:
--   Proposition 3.1 — variational principle on the self-reduction tree
-- statement:
--   For every strictly positive law $\mu=e^\Phi/Z_\Phi$ on $\{0,1\}^d$, with $\Phi$ normalized by $\Phi(0)=0$,
--   $$\log Z_\Phi=\max_\theta\Bigl(\sum_v\nu_\theta(v)H(\theta_v)+E_{\nu_\theta}\Phi\Bigr),\tag{3.4}$$
--   the maximum over branching rules $\theta$, and the unique maximizer is the vector $\theta=p$ of conditional marginal probabilities of $\mu$.
--
--   Stated as: $p$ is a branching rule attaining $\log Z_\Phi$; every branching rule gives a value at most $\log Z_\Phi$; and a branching rule attaining $\log Z_\Phi$ agrees with $p$ at every internal node.
--
--   Differences from the source:
--   - encoding: the unique maximizer is θ = p → p attains the maximum, and any maximizer equals p at every internal node (prefix of length < d); reason: a branching rule is determined by its values at internal nodes
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 13 (PDF 14), Proposition 3.1, (3.4)

import Definitions.Def_LogSupermodularBIS_Main_Variational

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Proposition 3.1 (Variational principle on the self-reduction tree), p. 13. -/
theorem proposition_3_1 {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (hΦ₀ : Φ (zeroConfig d) = 0) :
    IsBranchingRule d (condMarginalRule Φ) ∧
    treeObjective Φ (condMarginalRule Φ) = Real.log (potentialPartition Φ) ∧
    (∀ θ, IsBranchingRule d θ → treeObjective Φ θ ≤ Real.log (potentialPartition Φ)) ∧
    ∀ θ, IsBranchingRule d θ → treeObjective Φ θ = Real.log (potentialPartition Φ) →
      ∀ v : List Bool, v.length < d → θ v = condMarginalRule Φ v := by sorry

end LogSupermodularBIS.Main
