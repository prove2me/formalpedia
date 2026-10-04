-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_prop_6_1_b
-- name    : MeanFieldOpt.FullSupport.prop_6_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:30:23.792185+00:00
-- url     : https://prove2.me/theorems/55a991b8-6cbe-42b5-93c3-3f97f1811a12
-- title:
--   Proposition 6.1(b) — for $\gamma\in\mathsf{SF}_+$, $\partial_x\Phi(t,\cdot)$ is non-decreasing with $|\partial_x\Phi|\le1$
-- statement:
--   Let $\xi$ be a mixture, $f_0$ an admissible terminal condition (convex, continuous, even, non-negative, differentiable off $0$ with $0 \le f_0' \le 1$ on $(0,\infty)$), and $\gamma \in \mathsf{SF}_+$. Let $\Phi = \Phi^\gamma$ be the Cole–Hopf solution of the Parisi PDE (6.2). Then for every $t \in [0,1]$ the map $x \mapsto \partial_x\Phi(t,x)$ is non-decreasing, and
--
--   $$
--   |\partial_x\Phi(t,x)| \le 1 \qquad \text{for all } x \in \mathbb R .
--   $$
--
--   This is the a priori gradient bound behind the existence of strong solutions of the SDE (6.3) and behind the extension of $\Phi^\gamma$ to all $\gamma \in \mathscr L$.
--
--   **Formalization Note** $\partial_x\Phi$ is Lean's `deriv`. At $t = 1$, $\Phi(1,\cdot) = f_0$ may fail to be differentiable at $0$, where `deriv` returns $0$; this value lies between the one-sided derivatives, so the statement is unchanged.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 23, Proposition 6.1(b)

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_PhiSF

namespace MeanFieldOpt.FullSupport

/-- Proposition 6.1 (b) (arXiv:2001.00904v1, p. 23): for `γ ∈ SF₊`, `x ↦ ∂_xΦ(t, x)` is
non-decreasing for all `t ∈ [0,1]`, with `|∂_xΦ(t, x)| ≤ 1` for all `x`. -/
theorem prop_6_1_b (ξ : Mixture) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀) (d : SFData) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Monotone (deriv (PhiSF ξ f₀ d t)) ∧
      ∀ x : ℝ, |deriv (PhiSF ξ f₀ d t) x| ≤ 1 := by sorry

end MeanFieldOpt.FullSupport
