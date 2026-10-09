-- Prove2me | Theorems.Thm_GraphonGames_Existence_theorem_3_15_existence
-- name    : GraphonGames.Existence.theorem_3_15_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:36.920149+00:00
-- url     : https://prove2.me/theorems/544413d9-af66-4a4d-a72b-592b428b8c7f
-- title:
--   Theorem 3.15, p. 15 — under Assumptions 1, 4, 5 and √c_z‖W‖ < 1 a Nash equilibrium exists
-- statement:
--   Consider the static graphon game with graphon $w$ (integral operator $\mathbf W$), state map $b$, noise law $\mu_0$ and cost $J(\alpha,z)=\int f(b(\alpha,z)+\xi,\alpha,z)\,\mu_0(d\xi)$. Assume
--
--   1. Assumption 1: $|b(\alpha,z)-b(\alpha',z')|^2\le c_\alpha|\alpha-\alpha'|^2+c_z|z-z'|^2$, and $\mu_0$ is a mean-zero probability law with finite second moment;
--   2. Assumption 4: $J(\cdot,z)$ is $C^1$ and $\ell_c$-strongly convex uniformly in $z$, and $\partial_\alpha J$ is $\ell_J$-Lipschitz in $z$;
--   3. Assumption 5: $|b|\le c_0$ for a finite $c_0>0$;
--   4. $\sqrt{c_z}\,\|\mathbf W\|<1$.
--
--   Then there is at least one Nash equilibrium: a profile $\hat\alpha\in L^2(I)$ whose aggregate $\mathbf Z\hat\alpha$ satisfies
--   $$J(\hat\alpha_x,(\mathbf Z\hat\alpha)_x)\le J(\beta,(\mathbf Z\hat\alpha)_x)\qquad\text{for }\lambda_I\text{-a.e. }x\in I\text{ and every }\beta\in\mathbb R.$$
--
--   Unlike the uniqueness result (Proposition 3.17), no smallness condition linking $\ell_J/\ell_c$ and $\|\mathbf W\|$ is needed; boundedness of $b$ replaces it.
--
--   **Formalization Note.** The equilibrium is the third bullet of Proposition 3.6, which the paper states is equivalent to Definition 3.4 under Assumption 4; Definition 3.4's Fubini-extension formulation is not formalized.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 15, Theorem 3.15

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Existence

theorem theorem_3_15_existence (b : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ) (μ0 : Measure ℝ)
    (cα cz ℓc ℓJ c0 : ℝ) (h1 : Asm1 b μ0 cα cz) (h4 : Asm4 (cost b f μ0) ℓc ℓJ) (h5 : Asm5 b c0)
    (w : I → I → ℝ) (hw : IsGraphon w) (hW : Real.sqrt cz * (opNorm w).toReal < 1) :
    ∃ α : I → ℝ, IsNash w b f μ0 α := by sorry

end GraphonGames.Existence
