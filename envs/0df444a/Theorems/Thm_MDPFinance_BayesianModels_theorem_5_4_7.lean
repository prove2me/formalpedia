-- Prove2me | Theorems.Thm_MDPFinance_BayesianModels_theorem_5_4_7
-- name    : MDPFinance.BayesianModels.theorem_5_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:28:06.49197+00:00
-- url     : https://prove2.me/theorems/6296f31c-9f57-4d3e-9abc-ac16ab40ee12
-- title:
--   Theorem 5.4.7 — value equality, Bayesian Model = information-based model
-- statement:
--   **Theorem 5.4.7.** For every $N$-stage policy $\pi$ of the Bayesian Model and $x \in E_X$,
--   $$
--   J_N^\pi(x) = \hat J_N^\pi(x,t_0), \qquad\text{and hence}\qquad J_N(x) = \hat J_N(x,t_0),
--   $$
--   where $t_0$ is the (constant) value of the sufficient statistic before any observation, and
--   $\hat J_N^\pi$/$\hat J_N$ are $\pi$'s value/the optimal value computed through the
--   information-based model's own reduced (fully-observed) machinery.
--
--   This is what licenses replacing the original, harder-to-analyze Bayesian Model (whose true state
--   $(x,\theta)$ is never fully observed) by the information-based model built from a sequential
--   sufficient statistic: the two models agree on every policy's value, and hence on the optimal
--   value, so optimizing one optimizes the other.
--
--   **Formalization Note.** The proof follows the same lines as
--   `MDPFinance.POMDP.theorem_5_3_2` (chunk `05a`)'s reduction from the general filtered model:
--   both sides recurse identically over the same disturbance law, since $\hat r,\hat g,\hat Q^Z$ are
--   exactly $r,g,Q^Z$ averaged against $\hat\mu(\cdot\mid t_n(\tilde h_n)) = \mu_n(\cdot\mid
--   \tilde h_n)$.
--
--   **Moderation note.** Both sides are in $[-\infty,\infty]$, under the chapter's standing Integrability Assumption (`hInt`). The draft compared a real supremum (a default $0$ when the policy values are unbounded above) with an extended-real one.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 162, Theorem 5.4.7

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior
import Definitions.Def_MDPFinance_BayesianModels_SuffStat
import Definitions.Def_MDPFinance_BayesianModels_Policy
import Definitions.Def_MDPFinance_BayesianModels_Objective
import Definitions.Def_MDPFinance_BayesianModels_InfoModel

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

/-- Theorem 5.4.7 (Bäuerle–Rieder, p. 162, PDF 176). Suppose `π ∈ Π̃_N`. Then it holds for
`x ∈ E_X`: `J_N^π(x) = Ĵ_N^π(x,t_0)` and `J_N(x) = Ĵ_N(x,t_0)`, where `t_0` is the (constant)
value of the sufficient statistic before any observation. The proof follows along the same lines
as the proof of Theorem 5.3.2 (`MDPFinance.POMDP.theorem_5_3_2`, chunk `05a`): both sides recurse
identically over the same disturbance law, since `r̂`/`ĝ`/`Q̂^Z` are exactly `r`/`g`/`Q^Z` averaged
against `μ̂(\cdot|t_n(h̃_n)) = μ_n(\cdot|h̃_n)` (`SuffStat.ht_suff`). Values in `[-∞,∞]`, under the
chapter's standing Integrability Assumption (p. 151). -/
theorem theorem_5_4_7 {EX Θ A Z I : Type*} [MeasurableSpace EX] [MeasurableSpace Θ]
    [MeasurableSpace A] [MeasurableSpace Z] [MeasurableSpace I] [Nonempty A] [Nonempty Z]
    (M : BayesModel EX Θ A Z) (Pf : M.Posterior) (S : SuffStat M Pf I)
    (Phihat : EX → I → A → Z → I) (hSeq : S.IsSequential Phihat) (Im : InfoModel M Pf S Phihat)
    (N : ℕ) (hInt : M.IntegrabilityAssumption N) (π : Policy EX A Z) (hπ : M.IsPolicy N π)
    (x : EX) :
    M.JNpi π N x = Im.JNpiHat π N x ∧
      M.JN N x = Im.Jhat N (x, S.t 0 (fun _ => x) (fun _ => Classical.arbitrary A)
        (fun _ => Classical.arbitrary Z)) := by sorry

end MDPFinance.BayesianModels
