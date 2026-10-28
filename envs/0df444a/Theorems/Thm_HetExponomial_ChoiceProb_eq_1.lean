-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_eq_1
-- name    : HetExponomial.ChoiceProb.eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:40.536014+00:00
-- url     : https://prove2.me/theorems/2e1e91e0-70aa-43da-bcb4-5c7bdd1fb5a3
-- title:
--   Equation (1), p. 6 — Q_i(u, λ) as an integral against f_i, and as ∫_0^∞ λ_i exp[−Σ_j λ_j (u_j − u_i + z)^+] dz
-- statement:
--   In the HEC model (see the definitions file), let $n\ge 2$, let $u\in\mathbb R^n$ be ideal utilities and let $\lambda_j>0$ be the error rates. The errors $z_j\sim\mathrm{Exp}(\lambda_j)$ are independent. For every choice $i\in N$, the choice probability $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ satisfies
--   $$
--   Q_i(\mathbf u,\boldsymbol\lambda)=\int_0^\infty \prod_{j\in N,\,j\ne i}\big[1-F_j(u_j-u_i+z)\big]\,f_i(z)\,dz
--   =\int_0^\infty \lambda_i\exp\Big[-\sum_{j\in N}\lambda_j\,(u_j-u_i+z)^+\Big]\,dz .
--   $$
--   Here $f_j$ and $F_j$ are the exponential density and distribution function, set to $0$ on the negative half-line, and $x^+=\max(x,0)$.
--
--   This is equation (1) of the paper. It turns the probability into a one-dimensional integral, which the proof of Theorem 1 evaluates in closed form.
--
--   **Formalization Note** Both equalities are stated as a conjunction. $\int_0^\infty$ is the Bochner integral over the open half-line $(0,\infty)$, which agrees with $[0,\infty)$ because a point has Lebesgue measure zero.
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 6, equation (1)

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb

theorem eq_1 {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n) :
    choiceProb u lam i =
        ∫ z in Set.Ioi 0,
          (∏ j ∈ Finset.univ.erase i, (1 - cdfExp (lam j) (u j - u i + z))) * pdfExp (lam i) z ∧
      choiceProb u lam i =
        ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) := by sorry

end HetExponomial.ChoiceProb
