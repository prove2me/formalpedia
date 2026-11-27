-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_2
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:37:21.715282+00:00
-- url     : https://prove2.me/theorems/70d5757a-b238-4a85-832a-4439ae76c90b
-- title:
--   Theorem 2, p. 8 — Q_i is continuous in u, all partials exist and are continuous, and equal (4)
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. Fix the error rates $\boldsymbol\lambda$ and a choice $i$. Then
--
--   1. $\mathbf u\mapsto Q_i(\mathbf u)$ is continuous on $\mathbb R^n$;
--   2. every partial derivative $\partial Q_i/\partial u_j$ exists at every $\mathbf u\in\mathbb R^n$ and is a continuous function of $\mathbf u$;
--   3. the partial derivatives are given by (4):
--   $$
--   \frac{\partial Q_i(\mathbf u)}{\partial u_j}=\begin{cases}-\lambda_jQ_i(\mathbf u) & j\ne i,\ u_j\ge u_i,\\ L_iG_i(\mathbf u)-\lambda_iQ_i(\mathbf u) & j=i,\\ -\lambda_iQ_j(\mathbf u) & j\ne i,\ u_j\le u_i.\end{cases}
--   $$
--
--   When $j\ne i$ and $u_j=u_i$ both cross-partial formulas hold. Although the closed form of Theorem 1 is built from terms $G_k$ that jump when ideal utilities cross, the choice probabilities are continuously differentiable; this underlies the demand elasticities (7), the consumer surplus of Theorem 3 and the first-order conditions (12) of the pricing game.
--
--   **Formalization Note** The partial derivative in $u_j$ is the derivative at $t=u_j$ of $t\mapsto Q_i(\mathbf u\text{ with }u_j\text{ replaced by }t)$ (`HasDerivAt`); its continuity is stated for `partialU`, the `deriv` of that restriction, as a function on $\mathbb R^n$.
--
--   Differences from the source:
--   - encoding: partial derivative ∂Q_i/∂u_j → HasDerivAt of the coordinate restriction t ↦ Q_i(u with u_j := t) at u_j; continuity of its deriv as a function of u; reason: the standard definition of a partial derivative; the same claim
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 8, Theorem 2, (4); proof pp. 44–46

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_2 {n : ℕ} (hn : 2 ≤ n) (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) :
    Continuous (fun u => choiceProb u lam i) ∧
      (∀ j, Continuous (partialU (fun v => choiceProb v lam i) j)) ∧
      ∀ (u : Fin n → ℝ) (j : Fin n),
        (j ≠ i → u i ≤ u j →
            HasDerivAt (fun t => choiceProb (Function.update u j t) lam i)
              (-(lam j * choiceProb u lam i)) (u j)) ∧
          (j = i →
            HasDerivAt (fun t => choiceProb (Function.update u j t) lam i)
              (Lsum u lam i * G u lam i - lam i * choiceProb u lam i) (u j)) ∧
          (j ≠ i → u j ≤ u i →
            HasDerivAt (fun t => choiceProb (Function.update u j t) lam i)
              (-(lam i * choiceProb u lam j)) (u j)) := by sorry

end HetExponomial.ChoiceProb.Supplement
