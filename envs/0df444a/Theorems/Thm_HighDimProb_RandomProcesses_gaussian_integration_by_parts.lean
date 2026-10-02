-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_gaussian_integration_by_parts
-- name    : HighDimProb.RandomProcesses.gaussian_integration_by_parts
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T07:59:22.111952+00:00
-- url     : https://prove2.me/theorems/a95c54b1-497e-4f0a-986f-ab58362e4e56
-- title:
--   Gaussian integration by parts under absolute integrability
-- statement:
--   Let $G$ have the standard normal distribution, and let $f,f' : \mathbb R\to\mathbb R$ satisfy that $f$ is differentiable everywhere with derivative $f'$. Assume $f(G)$, $f'(G)$ and $Gf(G)$ are absolutely integrable. Then
--
--   $$\mathbb E[f'(G)]=\mathbb E[Gf(G)].$$
--
--   This identity is the one-dimensional analytic input to Gaussian interpolation and Slepian comparison. The explicit absolute-integrability assumptions make every expectation a genuine finite integral.
-- source:
--   Vershynin, High-Dimensional Probability (first edition), Lemma 7.2.3, pp. 162–163 (PDF pp. 170–171). https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf. Explicit regularity and integrability hypotheses specify the analytic form used here.

import Mathlib
open MeasureTheory ProbabilityTheory Filter

theorem HighDimProb.RandomProcesses.gaussian_integration_by_parts {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, f' x ∂gaussianReal 0 1) =
      ∫ x, x * f x ∂gaussianReal 0 1 := by sorry
