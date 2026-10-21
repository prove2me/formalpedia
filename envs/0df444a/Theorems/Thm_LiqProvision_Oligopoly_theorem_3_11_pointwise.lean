-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_theorem_3_11_pointwise
-- name    : LiqProvision.Oligopoly.theorem_3_11_pointwise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:36.729221+00:00
-- url     : https://prove2.me/theorems/1c0b9a86-9768-4dda-bc8c-0fa4c29e8ab1
-- title:
--   Proof of Theorem 3.11, (B.53)–(B.54), p. 28 — pointwise optimality of the ODE solution in η₋ and η₊
-- statement:
--   Assume the standing assumptions, Assumptions 2.1, 3.7 and 3.10, and let $p=P_*'$ be the increasing, continuously differentiable solution of (3.8). With $h=fg$, $H(x)=\int_{-\infty}^xh$, $\bar H(x)=\int_x^\infty h$, and
--   $$\eta_-(n,x,z)=(\gamma_dn-z)F(\xi)+H(\xi),\qquad\eta_+(n,x,z)=-(\gamma_dn-z)\bar F(\xi)-\bar H(\xi),\qquad\xi=z+\gamma_cn+\gamma_c(K-1)x,$$
--   and $p^{-1}$ the inverse of $p$ extended by $0$ on $[p(0-),p(0+)]$, one has for every $z\in\mathbb R$
--   $$\eta_-\big(n,n,p(n)\big)\ge\eta_-\big(n,p^{-1}(z),z\big)\quad(n<0),\qquad \eta_+\big(n,n,p(n)\big)\ge\eta_+\big(n,p^{-1}(z),z\big)\quad(n>0).$$
--
--   Dealer 1's goal functional against $(P_1,P_*,\dots,P_*)$ is $\int_{-\infty}^0\eta_-(n,p^{-1}(p_1(n)),p_1(n))\,dn+\int_0^\infty\eta_+(n,p^{-1}(p_1(n)),p_1(n))\,dn$ with $p_1=P_1'$ (B.50), so these inequalities give the optimality of $P_*$ against every deviation.
--
--   **Formalization Note.** The model objects are those of `LiqProvision.Oligopoly.Model`. The page states the inequalities at $z=p_1(n)$ for the marginal price $p_1$ of a deviation; since $p_1(n)$ can take any real value at a given $n$, the statement quantifies over all $z\in\mathbb R$.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 28, proof of Theorem 3.11, (B.51)–(B.54)

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

namespace LiqProvision.Oligopoly
theorem theorem_3_11_pointwise (M : Params) (hS : M.Standing) (h21 : M.Assumption21)
    (h37 : M.Assumption37) (p : ℝ → ℝ) (hp : IsODESol M p) (h310 : Assumption310 M p) :
    (∀ n < 0, ∀ z, etaNeg M n (pinv p z) z ≤ etaNeg M n n (p n)) ∧
      (∀ n > 0, ∀ z, etaPos M n (pinv p z) z ≤ etaPos M n n (p n)) := by sorry
end LiqProvision.Oligopoly
