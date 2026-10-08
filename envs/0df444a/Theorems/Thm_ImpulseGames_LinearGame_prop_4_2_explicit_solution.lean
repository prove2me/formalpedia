-- Prove2me | Theorems.Thm_ImpulseGames_LinearGame_prop_4_2_explicit_solution
-- name    : ImpulseGames.LinearGame.prop_4_2_explicit_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:28:19.485801+00:00
-- url     : https://prove2.me/theorems/5f0ad578-4f7a-4c7d-8f3f-1b4d8149df87
-- title:
--   Proposition 4.2 with (4.20): the explicit 8-uples solve (4.7)-(4.9), and $\varphi_2''$ changes sign once in $]x_2^*,\bar x_2[$
-- statement:
--   Assume the standing assumptions of Section 4.1, $c>0$, and let $\xi\in(0,\eta)$ be the zero of $F$ in (4.17). For every $\tilde s\in\mathbb R$ let $(A_{11},A_{12},A_{21},A_{22},\bar x_1,\bar x_2,x_1^*,x_2^*)$ be given by (4.20)-(4.21), and $\varphi_1,\varphi_2$ by (4.5). Then the order conditions
--   $$\bar x_1<x_1^*<\bar x_2,\qquad \bar x_1<x_2^*<\bar x_2\tag{4.7}$$
--   hold, together with
--   $$\begin{aligned}&\varphi_1'(x_1^*)=\lambda,\ \varphi_1''(x_1^*)\le0,\quad \varphi_1'(\bar x_1)=\lambda,\\ &\varphi_1(\bar x_1)=\varphi_1(x_1^*)-c-\lambda(x_1^*-\bar x_1),\quad \varphi_1(\bar x_2)=\varphi_1(x_2^*)+\tilde c+\tilde\lambda(\bar x_2-x_2^*),\end{aligned}\tag{4.8}$$
--   $$\begin{aligned}&\varphi_2'(x_2^*)=-\lambda,\ \varphi_2''(x_2^*)\le0,\quad \varphi_2'(\bar x_2)=-\lambda,\\ &\varphi_2(\bar x_1)=\varphi_2(x_1^*)+\tilde c+\tilde\lambda(x_1^*-\bar x_1),\quad \varphi_2(\bar x_2)=\varphi_2(x_2^*)-c-\lambda(\bar x_2-x_2^*).\end{aligned}\tag{4.9}$$
--   Moreover there is $\tilde x\in]x_2^*,\bar x_2[$ such that $\varphi_2''<0$ on $]\bar x_1,\tilde x[$ and $\varphi_2''>0$ on $]\tilde x,\bar x_2[$.
--
--   These are the optimality, smooth-pasting and continuous-pasting conditions that make the functions $\tilde V_1,\tilde V_2$ of Definition 4.1 regular enough for the verification theorem.
--
--   **Formalization Note.** Proposition 4.2 asserts the existence of "a family" of solutions and a property of "each of such 8-uples"; following Remark 4.4 and the proof, which treats the family (4.20) indexed by $\tilde s$, the statement is made for every member of that family. Derivatives are Mathlib's `deriv` of the explicit functions. The hypothesis $c>0$ is added as in (4.17).
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Proposition 4.2 and Definition 4.1 (p. 15), Remark 4.4, (4.20)-(4.21) (p. 17)

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Candidates

namespace ImpulseGames.LinearGame

/-- Proposition 4.2 (p. 15) for the explicit family (4.20)–(4.21) of Remark 4.4 (p. 17): for every
`s̃ ∈ ℝ`, the 8-uple `(A₁₁, A₁₂, A₂₁, A₂₂, x̄₁, x̄₂, x₁*, x₂*)` of (4.20) satisfies the order
conditions (4.7) and the pasting conditions (4.8a)–(4.8d), (4.9a)–(4.9d); moreover there is
`x̃ ∈ ]x₂*, x̄₂[` with `φ₂'' < 0` on `]x̄₁, x̃[` and `φ₂'' > 0` on `]x̃, x̄₂[`. -/
theorem prop_4_2_explicit_solution (M : Model) (hM : M.Standing) (hc : 0 < M.c)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 (eta M)) (hFξ : F M ξ = 0) (s : ℝ) :
    -- (4.7)
    (xbar M ξ s 1 < xstar M ξ s 1 ∧ xstar M ξ s 1 < xbar M ξ s 2) ∧
    (xbar M ξ s 1 < xstar M ξ s 2 ∧ xstar M ξ s 2 < xbar M ξ s 2) ∧
    -- (4.8a)
    (deriv (phiOne M ξ s) (xstar M ξ s 1) = M.lam ∧
      deriv (deriv (phiOne M ξ s)) (xstar M ξ s 1) ≤ 0) ∧
    -- (4.8b)
    deriv (phiOne M ξ s) (xbar M ξ s 1) = M.lam ∧
    -- (4.8c)
    phiOne M ξ s (xbar M ξ s 1) =
      phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - xbar M ξ s 1) ∧
    -- (4.8d)
    phiOne M ξ s (xbar M ξ s 2) =
      phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (xbar M ξ s 2 - xstar M ξ s 2) ∧
    -- (4.9a)
    (deriv (phiTwo M ξ s) (xstar M ξ s 2) = -M.lam ∧
      deriv (deriv (phiTwo M ξ s)) (xstar M ξ s 2) ≤ 0) ∧
    -- (4.9b)
    deriv (phiTwo M ξ s) (xbar M ξ s 2) = -M.lam ∧
    -- (4.9c)
    phiTwo M ξ s (xbar M ξ s 1) =
      phiTwo M ξ s (xstar M ξ s 1) + M.ct + M.lamt * (xstar M ξ s 1 - xbar M ξ s 1) ∧
    -- (4.9d)
    phiTwo M ξ s (xbar M ξ s 2) =
      phiTwo M ξ s (xstar M ξ s 2) - M.c - M.lam * (xbar M ξ s 2 - xstar M ξ s 2) ∧
    -- the inflection point of φ₂
    (∃ xt ∈ Set.Ioo (xstar M ξ s 2) (xbar M ξ s 2),
      (∀ y ∈ Set.Ioo (xbar M ξ s 1) xt, deriv (deriv (phiTwo M ξ s)) y < 0) ∧
      (∀ y ∈ Set.Ioo xt (xbar M ξ s 2), 0 < deriv (deriv (phiTwo M ξ s)) y)) := by sorry

end ImpulseGames.LinearGame
