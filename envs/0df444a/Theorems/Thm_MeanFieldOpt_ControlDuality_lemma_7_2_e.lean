-- Prove2me | Theorems.Thm_MeanFieldOpt_ControlDuality_lemma_7_2_e
-- name    : MeanFieldOpt.ControlDuality.lemma_7_2_e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:07:39.986561+00:00
-- url     : https://prove2.me/theorems/a92d1ec5-7a70-47db-b3d4-3cd5f927f557
-- title:
--   Lemma 7.2(e) — $0<\partial_x^2\Phi_\gamma(t',x)\le C(t,\gamma)$ for $t'\in[0,t]$
-- statement:
--   Let $\xi$ be a mixture that is not identically zero, $\gamma\in\mathsf{SF}_+$, and $\Phi_\gamma$ the Cole–Hopf solution of the Parisi PDE with $\Phi_\gamma(1,x)=|x|$. For every $t\in[0,1)$ there is a constant $C(t,\gamma)<\infty$ such that
--   $$0<\partial_x^2\Phi_\gamma(t',x)\le C(t,\gamma)\qquad\text{for all }x\in\mathbb R\text{ and all }t'\in[0,t].$$
--
--   The positive lower bound makes the second derivative of the Legendre transform finite, and the uniform upper bound makes the optimal feedback control bounded on $[0,t]$.
--
--   **Formalization Note** The constant is chosen after $t$ and before $x$ and $t'$, as on the page. The hypothesis that some $c_k\neq0$ is added: for $\xi\equiv0$, $\partial_x^2\Phi_\gamma=0$ away from $x=0$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 35, Lemma 7.2 (e)

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_ColeHopf

open Set

namespace MeanFieldOpt.ControlDuality

/-- Lemma 7.2 (e) (arXiv:2001.00904v1, p. 35), for a mixture that is not identically zero: for
every `t ∈ [0, 1)` there is a constant `C(t, γ) < ∞` such that
`0 < ∂_x² Φ_γ(t', x) ≤ C(t, γ)` for all `x ∈ ℝ` and all `t' ∈ [0, t]`. -/
theorem lemma_7_2_e (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (d : SFData) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∃ C : ℝ, ∀ x : ℝ, ∀ t' ∈ Icc (0 : ℝ) t,
      0 < deriv (deriv (PhiSF ξ d t')) x ∧ deriv (deriv (PhiSF ξ d t')) x ≤ C := by sorry

end MeanFieldOpt.ControlDuality
