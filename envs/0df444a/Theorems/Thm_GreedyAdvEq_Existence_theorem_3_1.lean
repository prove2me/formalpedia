-- Prove2me | Theorems.Thm_GreedyAdvEq_Existence_theorem_3_1
-- name    : GreedyAdvEq.Existence.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:11.156562+00:00
-- url     : https://prove2.me/theorems/bffc4776-7310-4c19-9db0-29b44bed3dde
-- title:
--   Theorem 3.1, p. 10 (existence) — every C² b-bounded f with L-Lipschitz Hessian has an (ε⋆, σ)-greedy adversarial equilibrium for some 0 < ε⋆ ≤ ε, when σ ≤ 1/√(εd)
-- statement:
--   Let $d\ge1$, let $\varepsilon,\sigma>0$ with
--   $$\sigma\le\frac1{\sqrt{\varepsilon d}},$$
--   and let $f:\mathbb R^d\times\mathbb R^d\to\mathbb R$ be $C^2$, $b$-bounded ($|f(x,y)|\le b$) and with $L$-Lipschitz Hessian, for some $b,L>0$. Then there are $\varepsilon^\star$ with $0<\varepsilon^\star\le\varepsilon$ and a point $(x^\star,y^\star)\in\mathbb R^d\times\mathbb R^d$ which is an $(\varepsilon^\star,\sigma)$-greedy adversarial equilibrium of $f$:
--   1. $y^\star$ is an $(\varepsilon^\star,\sqrt{L\varepsilon^\star})$-approximate local maximum of $f(x^\star,\cdot)$, and
--   2. $x^\star$ is an $(\varepsilon^\star,\sigma)$-approximate local minimum of the greedy max $g_{\varepsilon^\star}(\cdot,y^\star)$, in the sense of Definition 2.3.
--
--   This is the existence half of the paper's main result: unlike global or local min-max points, greedy adversarial equilibria exist for every smooth bounded objective, with no convexity, concavity or monotonicity assumption.
--
--   **Formalization Note.** Only the first two sentences of Theorem 3.1 are formalized; the algorithmic sentences (an algorithm succeeding with probability $9/10$ using polynomially many oracle calls) are not. $d\ge1$ is added ($\sigma\le1/\sqrt{\varepsilon d}$ is meaningless at $d=0$). The theorem is stated for every $b,L>0$ for which $f$ satisfies the model, and the equilibrium uses that $L$ (Definition 2.5 is relative to the Lipschitz constant). The conclusion $\varepsilon^\star>0$ is not printed but is what the proof delivers ($\varepsilon^\star=\varepsilon_0(1+\delta)^{2i^\star}$); it makes the statement stronger. All conventions are those of the Setting: the joint Euclidean norm, quadratic-form eigenvalue bounds, the directional reading of Definition 2.1, integrability and asserted derivatives in Definition 2.3.
-- source:
--   Mangoubi, Vishnoi, Greedy Adversarial Equilibrium, arXiv:2006.12363v4, p. 10, Theorem 3.1 (first two sentences)

import Mathlib
import Definitions.Def_GreedyAdvEq_Existence_Setting

namespace GreedyAdvEq.Existence

theorem theorem_3_1 (d : ℕ) (hd : 0 < d) (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 < σ)
    (hσε : σ ≤ 1 / Real.sqrt (ε * d))
    (f : E d → E d → ℝ) (b L : ℝ) (hb : 0 < b) (hL : 0 < L) (hf : IsModel f b L) :
    ∃ εs : ℝ, 0 < εs ∧ εs ≤ ε ∧ ∃ xs ys : E d, IsGAE f L εs σ xs ys := by sorry

end GreedyAdvEq.Existence
