-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_3
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:37:57.040435+00:00
-- url     : https://prove2.me/theorems/0fdcb271-c6ff-41cf-9658-fee198abf498
-- title:
--   Theorem 3, p. 11 — E[max_i (u_i − z_i)] = u_m − Q_m/λ_m for every m with u_m = u_max, and ∂CS/∂u_i = Q_i
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. Let the **expected consumer surplus** be
--   $$
--   CS(\mathbf u,\boldsymbol\lambda)=E\Big[\max_{i\in N}(u_i-z_i)\Big].
--   $$
--   Then
--
--   1. for every choice $m$ with maximal ideal utility ($u_m=u_{\max}=\max_j u_j$),
--   $$
--   CS(\mathbf u,\boldsymbol\lambda)=u_m-\frac{1}{\lambda_m}\,Q_m(\mathbf u,\boldsymbol\lambda);\qquad(8)
--   $$
--   2. for every $\mathbf u$ and every $i\in N$, $\partial CS(\mathbf u,\boldsymbol\lambda)/\partial u_i=Q_i(\mathbf u,\boldsymbol\lambda)$.
--
--   The formula gives welfare in closed form, and the derivative identity says that improving the most popular choice raises expected consumer surplus the most. Ties for the maximum are allowed: by Corollary 1(b) every tied $m$ gives the same value.
--
--   **Formalization Note** $CS$ is the Bochner integral of $\max_i(u_i-z_i)$ (`⨆ i`) under the published error law. The derivative is the derivative of $t\mapsto CS$ with $u_i$ replaced by $t$, at $t=u_i$.
--
--   Differences from the source:
--   - encoding: E[max_i (u_i − z_i)] → Bochner integral of ⨆ i, (u i − z i) under errorLaw; reason: the expectation under the product of the exponential laws; the maximum is integrable, so no junk value arises
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 11, Theorem 3, (8); §3.2 definition of CS, p. 11; proof pp. 47–49

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_3 {n : ℕ} (hn : 2 ≤ n) (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (u : Fin n → ℝ) :
    (∀ m, (∀ j, u j ≤ u m) →
        consumerSurplus u lam = u m - 1 / lam m * choiceProb u lam m) ∧
      ∀ i, HasDerivAt (fun t => consumerSurplus (Function.update u i t) lam)
        (choiceProb u lam i) (u i) := by sorry

end HetExponomial.ChoiceProb.Supplement
