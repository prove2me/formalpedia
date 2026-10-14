-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_lemma_A_2
-- name    : GPhNGIDiffusion.EMError.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:56.749134+00:00
-- url     : https://prove2.me/theorems/18f1b04b-0376-40ad-8ebc-882fd0cfcb30
-- title:
--   Lemma A.2: $\tilde P_\eta f$ is $\|f\|_\infty(1+C_{\mathrm{op}}\eta)\|\sigma^{-1}\|^2_{\mathrm{op}}\|\sigma\|_{\mathrm{op}}\eta^{-1/2}d^{1/2}$-Lipschitz; strong Feller and irreducible
-- statement:
--   Let $\tilde P_\eta$ be the one-step transition of the Euler–Maruyama chain (1.2) of a model, with step $\eta>0$, and let $C_{\mathrm{op}}=\|R\|_{\mathrm{op}}+\|(R-\alpha I)pe'\|_{\mathrm{op}}$. Then:
--
--   1. for every bounded measurable $f:\mathbb R^d\to\mathbb R$ and all $x,y\in\mathbb R^d$,
--   $$
--   |\tilde P_\eta f(x)-\tilde P_\eta f(y)|\le \|f\|_\infty(1+C_{\mathrm{op}}\eta)\|\sigma^{-1}\|_{\mathrm{op}}^2\|\sigma\|_{\mathrm{op}}\eta^{-1/2}d^{1/2}\,|x-y|;
--   $$
--   2. the chain is strong Feller: $\tilde P_\eta f$ is continuous for every bounded measurable $f$;
--   3. the chain is irreducible: $\tilde P_\eta^k(x,B(y,r))>0$ for all $x,y\in\mathbb R^d$, $r>0$ and $k\ge1$, where $B(y,r)$ is the closed ball.
--
--   Strong Feller property and irreducibility give uniqueness of the invariant measure of the chain in Proposition 2.1.
--
--   **Formalization Note** The paper states the bound as $\|\nabla\tilde P_\eta f\|_\infty\le\cdots$. The drift $g$ is not differentiable on $\{e'x=0\}$, so the gradient of $\tilde P_\eta f$ need not exist everywhere; the bound is stated in the equivalent Lipschitz form. $\|f\|_\infty$ is the essential supremum (§1.4): the bound holds for every $K$ with $|f|\le K$ almost everywhere. $\sigma$ is invertible by the uniform ellipticity of the model.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 24, Lemma A.2; proof p. 27

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

/-- Lemma A.2, p. 24, with the gradient bound in Lipschitz form: for every step `η > 0` and every
bounded measurable `f` with `‖f‖_∞ ≤ K` (essential supremum),
`|P̃_η f(x) − P̃_η f(y)| ≤ K(1 + C_op η)‖σ⁻¹‖²_op‖σ‖_op η^{−1/2} d^{1/2} |x − y|`;
`P̃_η f` is continuous (strong Feller); and the chain is irreducible:
`P̃^k_η(x, B(y, r)) > 0` for all `x, y`, `r > 0`, `k ≥ 1`. -/
theorem lemma_A_2 {d : ℕ} (M : Model d) (η : ℝ) (hη : 0 < η) :
    (∀ (f : EthierKurtz.SDEState d → ℝ) (K : ℝ), Measurable f → (∃ K' : ℝ, ∀ x, |f x| ≤ K') →
        (∀ᵐ x ∂volume, |f x| ≤ K) → ∀ x y,
          |emOp M.drift M.σ η f x - emOp M.drift M.σ η f y| ≤
            K * (1 + M.Cop * η) * opNorm M.σ⁻¹ ^ 2 * opNorm M.σ * η ^ (-(1 / 2 : ℝ))
              * Real.sqrt d * ‖x - y‖) ∧
    (∀ f : EthierKurtz.SDEState d → ℝ, Measurable f → (∃ K' : ℝ, ∀ x, |f x| ≤ K') →
        Continuous (emOp M.drift M.σ η f)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ (x y : EthierKurtz.SDEState d) (r : ℝ), 0 < r →
        0 < emLaw M.drift M.σ η (Measure.dirac x) k (Metric.closedBall y r)) := by sorry

end GPhNGIDiffusion.EMError
