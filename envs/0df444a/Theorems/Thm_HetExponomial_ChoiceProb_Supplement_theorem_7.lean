-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_7
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:39:20.898912+00:00
-- url     : https://prove2.me/theorems/b6c7127e-892a-49e1-aab7-70a7a261ab62
-- title:
--   Theorem 7, p. 25 — the monopolist's revenue R(p), p_l = 0, attains its maximum at a finite price vector
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. In the pricing model, product $i$ has ideal utility $u_i=\alpha_i-\beta p_i$ at price $p_i$, with intrinsic desirability $\alpha_i\in\mathbb R$ and price sensitivity $\beta>0$; market size is $1$ and marginal costs are $0$. The monopolist sells all $n$ choices except one, the **outside option** $l$, whose price is fixed at $p_l=0$ (so $u_l=\alpha_l$), and its expected revenue is
--   $$
--   R(\mathbf p)=\sum_{i=1}^n p_i\,Q_i(\mathbf p),\qquad(10)
--   $$
--   where $Q_i(\mathbf p)$ is $Q_i$ at $u_i=\alpha_i-\beta p_i$. **Theorem 7** (existence of finite optimal prices): there is a real price vector $\mathbf p^*$ with $p^*_l=0$ such that $R(\mathbf p)\le R(\mathbf p^*)$ for every real price vector $\mathbf p$ with $p_l=0$.
--
--   This justifies characterizing optimal prices by first-order conditions, which Theorem 8 does.
--
--   **Formalization Note** Prices are unrestricted real numbers apart from $p_l=0$, as in §5.
--
--   Differences from the source:
--   - reading: "the maximum revenue is achieved by a vector of finite prices" → ∃ p : Fin n → ℝ with p_l = 0 and R(q) ≤ R(p) for every q : Fin n → ℝ with q_l = 0; reason: the monopoly problem of §5 maximizes R over prices with p_l = 0 and no sign constraint; "finite" means a real vector attains the supremum
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 25, Theorem 7; model (10), p. 24; proof pp. 50–52

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_7 {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (l : Fin n) :
    ∃ p : Fin n → ℝ, IsOptimalMonopolyPrice α β lam l p := by sorry

end HetExponomial.ChoiceProb.Supplement
