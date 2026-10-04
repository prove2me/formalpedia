-- Prove2me | Theorems.Thm_MeanFieldOpt_ControlDuality_lemma_7_2_c
-- name    : MeanFieldOpt.ControlDuality.lemma_7_2_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:07:29.796235+00:00
-- url     : https://prove2.me/theorems/2ec13b39-60f2-475a-b18e-5afdd06fc296
-- title:
--   Lemma 7.2(c) — the range of $x\mapsto\partial_x\Phi_\gamma(t,x)$ is $(-1,1)$
-- statement:
--   Let $\xi$ be a mixture that is not identically zero, $\gamma\in\mathsf{SF}_+$, and $\Phi_\gamma$ the Cole–Hopf solution of the Parisi PDE with $\Phi_\gamma(1,x)=|x|$. For every $t\in[0,1)$, $\Phi_\gamma(t,\cdot)$ is differentiable and
--   $$\{\partial_x\Phi_\gamma(t,x):\ x\in\mathbb R\}=(-1,1).$$
--   In particular $|\partial_x\Phi_\gamma(t,x)|<1$.
--
--   This surjectivity onto $(-1,1)$ is what makes the Legendre transform $\Phi^*_\gamma(t,\cdot)$ finite and smooth exactly on the constraint interval $(-1,1)$ of the control problem.
--
--   **Formalization Note** The hypothesis that some $c_k\neq0$ is added: for $\xi\equiv0$, $\Phi_\gamma(t,x)=|x|$ and the range of its (Lean) derivative is $\{-1,0,1\}$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 35, Lemma 7.2 (c)

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_ColeHopf

open Set

namespace MeanFieldOpt.ControlDuality

/-- Lemma 7.2 (c) (arXiv:2001.00904v1, p. 35), for a mixture that is not identically zero: for
every `t ∈ [0, 1)`, `Φ_γ(t, ·)` is differentiable and the range of `x ↦ ∂_x Φ_γ(t, x)` is the open
interval `(−1, 1)`. -/
theorem lemma_7_2_c (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (d : SFData) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      Differentiable ℝ (PhiSF ξ d t) ∧ range (deriv (PhiSF ξ d t)) = Ioo (-1 : ℝ) 1 := by sorry

end MeanFieldOpt.ControlDuality
