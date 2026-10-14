-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_lemma_2_2
-- name    : GPhNGIDiffusion.EMError.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:36.227296+00:00
-- url     : https://prove2.me/theorems/7236861e-7159-4a02-9b80-0aa8629d4db4
-- title:
--   Lemma 2.2: Stein solution bounds $|f|\le C(1+|x|)$, $|\partial_if|\le C(1+|x|^2)$, $|\partial_{ij}f|\le C(1+|x|^3)$, $(1-\varsigma)$-Hölder $\nabla^2f$
-- statement:
--   Let $(P_t)$ be the transition function and $\mu$ an invariant probability measure of the limiting diffusion (1.1) of a model, with generator $\mathcal A$. For $h\in\mathrm{Lip}_0(1)$ let
--   $$
--   f=-\int_0^\infty\big(P_th-\mu(h)\big)\,dt
--   $$
--   be the solution of the Stein equation $\mathcal Af=h-\mu(h)$ (2.1). There is a constant $C>0$ such that for every $h\in\mathrm{Lip}_0(1)$: $f$ is twice continuously differentiable, $\mathcal Af(x)=h(x)-\mu(h)$ for all $x$, and for all $x$ and $1\le i,j\le d$,
--   $$
--   |f(x)|\le C(1+|x|),\qquad |\partial_if(x)|\le C(1+|x|^2),\qquad |\partial_{ij}f(x)|\le C(1+|x|^3). \tag{2.2}
--   $$
--   Moreover, for every $\varsigma\in(0,1)$ there is $C_\varsigma>0$ such that for every $h\in\mathrm{Lip}_0(1)$, all $1\le i,j\le d$ and all $x,y$ with $|y-x|<1$,
--   $$
--   |\partial_{ij}f(y)-\partial_{ij}f(x)|\le C_\varsigma(1+|x|^4)\,|y-x|^{1-\varsigma}. \tag{2.3}
--   $$
--
--   These regularity bounds are the analytic input of Stein's method in the proof of Theorem 1.2.
--
--   **Formalization Note** The paper takes this lemma from Gurvich (see also Braverman and Dai) and says "let $f$ be the solution"; here $f$ is pinned down by the semigroup representation (3.2) of the paper, and that $f$ is $C^2$ and solves (2.1) is part of the conclusion. The constants are uniform over $h\in\mathrm{Lip}_0(1)$, as the proof of Theorem 1.2 requires (it takes the supremum over $h$, p. 11). The supremum form of (2.3) is written without division. "For any small enough $\varsigma$" is rendered as all $\varsigma\in(0,1)$: for $|y-x|<1$ the bound weakens as $\varsigma$ grows, so the two readings are equivalent.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 9, Lemma 2.2, (2.1)-(2.3); p. 12, (3.2)

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

/-- Lemma 2.2, p. 9: let `f = −∫₀^∞ (P_t h − µ(h)) dt` be the solution of the Stein equation (2.1)
`Af = h − µ(h)` for `h ∈ Lip₀(1)`. There is `C > 0` such that for every `h ∈ Lip₀(1)`, `f` is `C²`,
solves (2.1), and for all `x` and `1 ≤ i, j ≤ d`, (2.2):
`|f(x)| ≤ C(1 + |x|)`, `|∂_i f(x)| ≤ C(1 + |x|²)`, `|∂_{ij} f(x)| ≤ C(1 + |x|³)`.
For every `ς ∈ (0, 1)` there is `C_ς > 0` such that (2.3)
`|∂_{ij} f(y) − ∂_{ij} f(x)| ≤ C_ς(1 + |x|⁴)|y − x|^{1−ς}` whenever `|y − x| < 1`. -/
theorem lemma_2_2 {d : ℕ} (M : Model d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hP : IsTransitionFunction M.drift M.σ P)
    (μ : Measure (EthierKurtz.SDEState d)) (hμ : IsInvariantMeasure P μ) :
    (∃ C : ℝ, 0 < C ∧ ∀ h : EthierKurtz.SDEState d → ℝ, IsLip1Zero h →
      ContDiff ℝ 2 (steinSolution P μ h) ∧
      (∀ x, generator M.drift M.σ (steinSolution P μ h) x = h x - ∫ y, h y ∂μ) ∧
      ∀ (x : EthierKurtz.SDEState d) (i j : Fin d),
        |steinSolution P μ h x| ≤ C * (1 + ‖x‖) ∧
        |partial1 (steinSolution P μ h) i x| ≤ C * (1 + ‖x‖ ^ 2) ∧
        |partial2 (steinSolution P μ h) i j x| ≤ C * (1 + ‖x‖ ^ 3)) ∧
    (∀ ς : ℝ, 0 < ς → ς < 1 → ∃ Cς : ℝ, 0 < Cς ∧
      ∀ h : EthierKurtz.SDEState d → ℝ, IsLip1Zero h →
        ∀ (x y : EthierKurtz.SDEState d), ‖y - x‖ < 1 → ∀ i j : Fin d,
          |partial2 (steinSolution P μ h) i j y - partial2 (steinSolution P μ h) i j x| ≤
            Cς * (1 + ‖x‖ ^ 4) * ‖y - x‖ ^ (1 - ς)) := by sorry

end GPhNGIDiffusion.EMError
