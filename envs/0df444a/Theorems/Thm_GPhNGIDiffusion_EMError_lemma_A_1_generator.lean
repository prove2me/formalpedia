-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_lemma_A_1_generator
-- name    : GPhNGIDiffusion.EMError.lemma_A_1_generator
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T17:54:48.497297+00:00
-- url     : https://prove2.me/theorems/ebee0fa8-e95b-431d-9485-97d763654226
-- title:
--   Lemma A.1 (generator bound): $\mathcal AV^\ell\le -c_1V^\ell+\breve c_\ell$
-- statement:
--   Let $V\in C^2(\mathbb R^d,\mathbb R_+)$ be a Lyapunov function of the limiting diffusion with constants $c_1,\breve c_1>0$, i.e. $V$ satisfies (A.5) $\hat c_1|y|^2\le V(y)\le \hat C|y|^2+\hat C'$, (A.6) $|\nabla V(y)|\le C(1+|y|)$ and (A.7) $\mathcal AV\le -c_1V+\breve c_1$, where
--   $$\mathcal Af(y)=\langle\nabla f(y),g(y)\rangle+\tfrac12\langle\sigma\sigma',\nabla^2f(y)\rangle_{HS}$$
--   is the generator (1.4). Then for every integer $\ell\ge1$ there is a constant $\breve c_\ell>0$, depending on $\ell$, such that
--   $$\mathcal AV^\ell(x)\le -c_1V^\ell(x)+\breve c_\ell\qquad\text{for all }x\in\mathbb R^d.$$
--
--   This is the first assertion of Lemma A.1; it is a deterministic calculus fact (chain rule $\mathcal A V^\ell=\ell V^{\ell-1}\mathcal AV+\frac{\ell(\ell-1)}2V^{\ell-2}\langle\sigma\sigma'\nabla V,\nabla V\rangle$ plus Young's inequality) and does not involve the diffusion process.
--
--   **Formalization Note** The milestone `lemma_A_1_moments` bundles this inequality with moment bounds that need the transition function of the diffusion; this statement isolates the purely analytic part so that it can be used for the Euler–Maruyama chain (Lemma A.4, Proposition 2.1) without assuming a transition function. For $\ell=1$ it is (A.7).
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 24, Lemma A.1 (first display $\mathcal AV^\ell(x)\le -c_1V^\ell(x)+\breve c_\ell$); proof p. 26 (Young's inequality with (A.5)-(A.7))

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Model
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_EulerMaruyama
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace GPhNGIDiffusion.EMError

/-- Lemma A.1 (first display), p. 24: for every Lyapunov function `V` of the model with constants
`c₁, c̆₁` (properties (A.5)–(A.7)) and every integer `ℓ ≥ 1` there is `c̆_ℓ > 0` with
`AV^ℓ(x) ≤ −c₁V^ℓ(x) + c̆_ℓ` for all `x`. -/
theorem lemma_A_1_generator {d : ℕ} (M : Model d)
    (V : EthierKurtz.SDEState d → ℝ) (c₁ c₁' : ℝ) (hV : IsLyapunovFn M V c₁ c₁')
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ cℓ : ℝ, 0 < cℓ ∧
      ∀ x, generator M.drift M.σ (fun y => V y ^ ℓ) x ≤ -c₁ * V x ^ ℓ + cℓ := by sorry

end GPhNGIDiffusion.EMError
