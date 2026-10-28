-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_theorem_1
-- name    : HetExponomial.ChoiceProb.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:51.301632+00:00
-- url     : https://prove2.me/theorems/1372321d-1a26-4ad1-857b-9590b77b6be8
-- title:
--   Theorem 1, p. 6 — under HEC, Q_i(u, λ) = G_i(u, λ) − Σ_{k∈W_i^−} (λ_i/L_k^+)·G_k(u, λ)
-- statement:
--   **Theorem 1 (closed-form HEC choice probabilities).** Consider $n\ge 2$ choices $N=\{1,\dots,n\}$. Choice $i$ has random utility $u_i-z_i$, where $u_i\in\mathbb R$ is its ideal utility. The errors $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$, are independent across choices. Let
--   $$
--   Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \ \forall j\in N,\ j\ne i\}
--   $$
--   be the probability that choice $i$ is utility-maximizing. Let $B_i=\{j: u_j\ge u_i\}$, $B_i^+=\{j: u_j>u_i\}$, $W_i^-=\{j: u_j<u_i\}$, $L_i=\sum_{j\in B_i}\lambda_j$, $L_i^+=\sum_{j\in B_i^+}\lambda_j$, and
--   $$
--   G_i(\mathbf u,\boldsymbol\lambda)=\frac{\lambda_i}{L_i}\exp\Big[-\sum_{j\in B_i}\lambda_j(u_j-u_i)\Big].
--   $$
--   Then for every $i\in N$,
--   $$
--   Q_i(\mathbf u,\boldsymbol\lambda)=G_i(\mathbf u,\boldsymbol\lambda)-\sum_{k\in W_i^-}\frac{\lambda_i}{L_k^+}\cdot G_k(\mathbf u,\boldsymbol\lambda).
--   $$
--
--   The theorem is the closed form of the HEC choice probabilities. It underlies every later result of the paper: continuity and derivatives (Theorem 2), consumer surplus (Theorem 3), and the pricing analysis. Ties among the ideal utilities are allowed. When all $u_j$ are equal it reduces to $Q_i=\lambda_i/(\lambda_1+\dots+\lambda_n)$. As an illustration (Table 1 of the paper), $u=(1,2,3)$ with $\lambda=(10,1,0.1)$ gives $Q\approx(27.13\%,57.59\%,15.28\%)$.
--
--   **Formalization Note** $Q_i$ is the probability of the event above under the product of the laws $\mathrm{Exp}(\lambda_j)$. It is neither the integral (1) nor the right-hand side. The paper defines $L_k^+$ only when $u_k<u_{\max}$; the Lean function is total, with value $0$ at a maximal choice. In the theorem it is evaluated only at $k\in W_i^-$, where $i\in B_k^+$ gives $L_k^+\ge\lambda_i>0$, so no extra hypothesis is needed. The hypothesis $n\ge 2$ is the paper's standing assumption (p. 4).
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 6, Theorem 1, equation (3)

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb

theorem theorem_1 {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n) :
    choiceProb u lam i =
      G u lam i - ∑ k ∈ strictlyWorse u i, lam i / Lplus u lam k * G u lam k := by sorry

end HetExponomial.ChoiceProb
