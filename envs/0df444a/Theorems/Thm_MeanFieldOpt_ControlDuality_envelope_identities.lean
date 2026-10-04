-- Prove2me | Theorems.Thm_MeanFieldOpt_ControlDuality_envelope_identities
-- name    : MeanFieldOpt.ControlDuality.envelope_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:28:29.580765+00:00
-- url     : https://prove2.me/theorems/8db7d9e8-6bf8-49ba-ada5-af9dece67498
-- title:
--   Proof of Lemma 7.3, p. 36 — envelope identities $\partial_z\Phi^*_\gamma=-x^*_t$, $\partial_z^2\Phi^*_\gamma=-1/\partial_x^2\Phi_\gamma(t,x^*_t)$
-- statement:
--   Let $\xi$ be a mixture that is not identically zero, $\gamma\in\mathsf{SF}_+$, $\Phi_\gamma$ the Cole–Hopf solution of the Parisi PDE with $\Phi_\gamma(1,x)=|x|$, and $\Phi^*_\gamma(t,z)=\inf_x\{\Phi_\gamma(t,x)-xz\}$. Let $t\in[0,1)$. There is a continuous, strictly increasing map $z\in(-1,1)\mapsto x^*_t(z)$ such that, for each $z\in(-1,1)$, $x^*_t(z)$ is the unique root $x$ of
--   $$\partial_x\Phi_\gamma(t,x)=z,$$
--   and for all $z\in(-1,1)$
--   $$\partial_z\Phi^*_\gamma(t,z)=-x^*_t(z),\qquad \partial_z^2\Phi^*_\gamma(t,z)=-\frac{1}{\partial_x^2\Phi_\gamma\big(t,x^*_t(z)\big)} .$$
--
--   These identities convert the Parisi PDE for $\Phi_\gamma$ into the HJB equation for $V$.
--
--   **Formalization Note** The page states these identities inside the proof of Lemma 7.3; they are stated here as a separate result. The hypothesis that some $c_k\neq0$ is added: for $\xi\equiv0$, $\Phi_\gamma(t,x)=|x|$, the equation $\partial_x\Phi_\gamma(t,x)=z$ has no root for $z\notin\{-1,0,1\}$, and $\Phi^*_\gamma(t,\cdot)\equiv0$ on $(-1,1)$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 36, proof of Lemma 7.3, first paragraph

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_Parisi

open Set

namespace MeanFieldOpt.ControlDuality

/-- Envelope identities (arXiv:2001.00904v1, p. 36, proof of Lemma 7.3, first paragraph), for a
mixture that is not identically zero. Let `t ∈ [0, 1)`. There is a continuous strictly increasing
map `z ∈ (−1, 1) ↦ x*_t(z)` such that `x*_t(z)` is the unique root `x` of `∂_x Φ_γ(t, x) = z`, and
for all `z ∈ (−1, 1)`:
`∂_z Φ*_γ(t, z) = −x*_t(z)` and `∂_z² Φ*_γ(t, z) = −1 / ∂_x² Φ_γ(t, x*_t(z))`. -/
theorem envelope_identities (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (d : SFData) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∃ xstar : ℝ → ℝ,
      ContinuousOn xstar (Ioo (-1 : ℝ) 1) ∧ StrictMonoOn xstar (Ioo (-1 : ℝ) 1) ∧
      ∀ z ∈ Ioo (-1 : ℝ) 1,
        deriv (PhiSF ξ d t) (xstar z) = z ∧
        (∀ x : ℝ, deriv (PhiSF ξ d t) x = z → x = xstar z) ∧
        HasDerivAt (PhiStar ξ d t) (-xstar z) z ∧
        HasDerivAt (deriv (PhiStar ξ d t))
          (-1 / deriv (deriv (PhiSF ξ d t)) (xstar z)) z := by sorry

end MeanFieldOpt.ControlDuality
