-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_corollary_1
-- name    : HetExponomial.ChoiceProb.Supplement.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:35:43.084595+00:00
-- url     : https://prove2.me/theorems/c6f1d438-dbd9-416e-9d11-8534a5f29384
-- title:
--   Corollary 1, p. 8 — Q_i/λ_i < Q_j/λ_j iff u_i < u_j, and Q_i/λ_i = Q_j/λ_j iff u_i = u_j
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. Then for all choices $i,j\in N$:
--
--   1. $\dfrac{Q_i}{\lambda_i}<\dfrac{Q_j}{\lambda_j}$ if and only if $u_i<u_j$;
--   2. $\dfrac{Q_i}{\lambda_i}=\dfrac{Q_j}{\lambda_j}$ if and only if $u_i=u_j$.
--
--   $$
--   \frac{Q_i(\mathbf u,\boldsymbol\lambda)}{\lambda_i}<\frac{Q_j(\mathbf u,\boldsymbol\lambda)}{\lambda_j}\iff u_i<u_j .
--   $$
--
--   This generalized monotonicity property says that the rate-normalized choice probabilities are ordered exactly as the ideal utilities. It shows that the two cross-partial formulas of Theorem 2 agree when $u_i=u_j$.
--
--   **Formalization Note** $Q_i$ is the published `choiceProb`, the probability of the event, not the closed form of Theorem 1.
--
--   Differences from the source: none.
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 8, Corollary 1

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem corollary_1 {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i j : Fin n) :
    (choiceProb u lam i / lam i < choiceProb u lam j / lam j ↔ u i < u j) ∧
      (choiceProb u lam i / lam i = choiceProb u lam j / lam j ↔ u i = u j) := by sorry

end HetExponomial.ChoiceProb.Supplement
