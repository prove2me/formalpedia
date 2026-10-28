-- Prove2me | Theorems.Thm_GreedyAdvEq_Existence_lemma_7_2
-- name    : GreedyAdvEq.Existence.lemma_7_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:08.490508+00:00
-- url     : https://prove2.me/theorems/8ce41479-d31d-444f-87a8-26d5c3075c99
-- title:
--   Lemma 7.2, p. 25, (24)–(25) — Algorithm 1 stops at an approximate local maximum of f(x, ·) (read with (25) + μ₄)
-- statement:
--   Let $f$ be $C^2$ and $b$-bounded with $L$-Lipschitz Hessian on $\mathbb R^d\times\mathbb R^d$, let $\mu_1,\mu_3>0$, $\mu_4\ge0$, and let the eigen-oracle return unit eigenpairs $(\lambda,v)$ of $\nabla_y^2 f$ with $\lambda\ge\lambda_{\max}(\nabla_y^2 f)-\mu_4$. If Algorithm 1 with inputs $x, y^0$ and $\varepsilon'>0$ terminates, then its output $y_{\mathrm{LocalMax}}$ satisfies
--   $$\|\nabla_y f(x,y_{\mathrm{LocalMax}})\|\le\varepsilon' \tag{24}$$
--   and
--   $$\lambda_{\max}\big(\nabla_y^2 f(x,y_{\mathrm{LocalMax}})\big)\le\sqrt{L\varepsilon'}+\mu_4. \tag{25}$$
--
--   This is the first half of Lemma 7.2: the max-player's subroutine always returns an approximate local maximum of $f(x,\cdot)$. It yields condition (6) of a greedy adversarial equilibrium at the output of the full algorithm.
--
--   **Formalization Note.** The page prints (25) without $+\mu_4$; since the stopping test (line 8) uses the approximate eigenvalue $\lambda\ge\lambda_{\max}-\mu_4$, stopping gives only $\lambda_{\max}\le\sqrt{L\varepsilon'}+\mu_4$, which is the proof's own (29). The statement is posed in that corrected form; it is the printed (25) when $\mu_4=0$. Termination is a hypothesis (the output is undefined otherwise). The second half of Lemma 7.2, (26)–(27) about Algorithm 2, is not formalized in this mission. $\lambda_{\max}$ bounds are quadratic-form bounds.
-- source:
--   Mangoubi, Vishnoi, Greedy Adversarial Equilibrium, arXiv:2006.12363v4, p. 25, Lemma 7.2, (24)–(25), with (29)

import Mathlib
import Definitions.Def_GreedyAdvEq_Existence_Setting
import Definitions.Def_GreedyAdvEq_Existence_Algorithm1

namespace GreedyAdvEq.Existence

theorem lemma_7_2 (d : ℕ) (f : E d → E d → ℝ) (b L : ℝ) (hb : 0 < b) (hL : 0 < L)
    (hf : IsModel f b L) (Eig : E d → E d → ℝ × E d) (μ₁ μ₃ μ₄ : ℝ)
    (hμ₁ : 0 < μ₁) (hμ₃ : 0 < μ₃) (hμ₄ : 0 ≤ μ₄) (hEig : IsEigOracle f Eig μ₄)
    (x y0 : E d) (ε' : ℝ) (hε' : 0 < ε') (hterm : Alg1Terminates f L Eig μ₁ μ₃ x y0 ε') :
    ‖gradY f x (alg1Out f L Eig μ₁ μ₃ x y0 ε')‖ ≤ ε' ∧
      ∀ v : E d, hessY f x (alg1Out f L Eig μ₁ μ₃ x y0 ε') v v ≤
        (Real.sqrt (L * ε') + μ₄) * ‖v‖ ^ 2 := by sorry

end GreedyAdvEq.Existence
