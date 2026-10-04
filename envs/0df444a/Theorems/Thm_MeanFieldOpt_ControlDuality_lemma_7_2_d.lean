-- Prove2me | Theorems.Thm_MeanFieldOpt_ControlDuality_lemma_7_2_d
-- name    : MeanFieldOpt.ControlDuality.lemma_7_2_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:07:15.054929+00:00
-- url     : https://prove2.me/theorems/41f3aece-6afc-4659-8e4a-24115ce522b7
-- title:
--   Lemma 7.2(d) — $\partial_x\Phi_\gamma(t,\cdot)$ is strictly increasing
-- statement:
--   Let $\xi$ be a mixture that is not identically zero, $\gamma\in\mathsf{SF}_+$, and $\Phi_\gamma$ the Cole–Hopf solution of the Parisi PDE with $\Phi_\gamma(1,x)=|x|$. For every $t\in[0,1)$, $\Phi_\gamma(t,\cdot)$ is differentiable and
--   $$x\mapsto\partial_x\Phi_\gamma(t,x)\ \text{is strictly increasing on }\mathbb R .$$
--
--   Thus $\Phi_\gamma(t,\cdot)$ is strictly convex, so the equation $\partial_x\Phi_\gamma(t,x)=z$ has at most one root.
--
--   **Formalization Note** The hypothesis that some $c_k\neq0$ is added: for $\xi\equiv0$, $\Phi_\gamma(t,x)=|x|$ is not strictly convex.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 35, Lemma 7.2 (d)

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_ColeHopf

open Set

namespace MeanFieldOpt.ControlDuality

/-- Lemma 7.2 (d) (arXiv:2001.00904v1, p. 35), for a mixture that is not identically zero: for
every `t ∈ [0, 1)`, `Φ_γ(t, ·)` is differentiable and `∂_x Φ_γ(t, ·)` is strictly increasing. -/
theorem lemma_7_2_d (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (d : SFData) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      Differentiable ℝ (PhiSF ξ d t) ∧ StrictMono (deriv (PhiSF ξ d t)) := by sorry

end MeanFieldOpt.ControlDuality
