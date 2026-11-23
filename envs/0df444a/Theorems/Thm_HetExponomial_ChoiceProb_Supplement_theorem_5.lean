-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_5
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:38:19.935414+00:00
-- url     : https://prove2.me/theorems/1e55c4d6-407a-4447-8ed3-f13ab91c46a4
-- title:
--   Theorem 5, p. 13 — for fixed λ, u ↦ Q_i(u, λ) is log-concave on ℝ^n
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. Fix the error rates $\boldsymbol\lambda$. For every choice $i$, the map $\mathbf u\mapsto Q_i(\mathbf u,\boldsymbol\lambda)$ is log-concave on $\mathbb R^n$: for all $\mathbf u,\mathbf v\in\mathbb R^n$ and $a,b\ge 0$ with $a+b=1$,
--   $$
--   Q_i(\mathbf u,\boldsymbol\lambda)^a\,Q_i(\mathbf v,\boldsymbol\lambda)^b\le Q_i(a\mathbf u+b\mathbf v,\boldsymbol\lambda).
--   $$
--
--   With linear-in-parameters ideal utilities, this makes the log-likelihood concave in the utility parameters for fixed error rates, so maximum likelihood estimation is a concave program.
--
--   **Formalization Note** Log-concavity is the published platform predicate `ConvexOptimization.LogConcaveOn` on `Set.univ` (nonnegativity plus the power-form inequality above). Since $Q_i>0$, this is equivalent to concavity of $\log Q_i$.
--
--   Differences from the source:
--   - encoding: Q_i(·, λ) logconcave → LogConcaveOn Set.univ (power form Q(u)^a Q(v)^b ≤ Q(a u + b v)); reason: equivalent to concavity of log Q_i because Q_i > 0
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 13, Theorem 5; proof p. 49 (via Theorem 4, Prékopa)

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_LogConcaveOn

namespace HetExponomial.ChoiceProb.Supplement

open HetExponomial.ChoiceProb

theorem theorem_5 {n : ℕ} (hn : 2 ≤ n) (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) :
    ConvexOptimization.LogConcaveOn Set.univ (fun u : Fin n → ℝ => choiceProb u lam i) := by sorry

end HetExponomial.ChoiceProb.Supplement
