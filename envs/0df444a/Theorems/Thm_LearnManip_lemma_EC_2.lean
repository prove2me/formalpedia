-- Prove2me | Theorems.Thm_LearnManip_lemma_EC_2
-- name    : LearnManip.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:11.189006+00:00
-- url     : https://prove2.me/theorems/35af7796-1cb9-4f48-a08b-b57223e4a818
-- title:
--   Lemma EC.2, p.ec6 — normal prior, Gaussian signal: the posterior and the law of $\mu^q$
-- statement:
--   Let $\theta\sim N(\mu,s)$ with $s\ge0$, and let $Z^q=\theta q+B_q$ with $B_q\sim N(0,q)$, $q\ge0$. For almost every value $z$ of the signal, the posterior of $\theta$ given $Z^q=z$ is
--   $$N\Bigl(\frac{\mu+sz}{1+sq},\ \frac{s}{1+sq}\Bigr),$$
--   so these are the posterior mean and variance. Unconditional on the signal, the posterior mean $(\mu+sZ^q)/(1+sq)$ has law
--   $$N\Bigl(\mu,\ \frac{s^2q}{1+sq}\Bigr).$$
--
--   This gives the undistorted learning model (2)–(3) on which the mission rests. The degenerate cases $s=0$ and $q=0$ are included.
--
--   Differences from the source:
--   - reading: a given q ∈ R → q ∈ ℝ₊; reason: the model's own range (p.7): q is a variance
--   - encoding: the observation process Z^q of the SDE (1) → the terminal value Z^q with likelihood N(θq, q); reason: (2) uses only this value, which is sufficient for the path
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Lemma EC.2, p.ec6 (PDF 45)

import Mathlib
import Definitions.Def_LearnManip_postVar
import Definitions.Def_LearnManip_meanVar
import Definitions.Def_LearnManip_signalKernel

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- Lemma EC.2, p.ec6 (PDF 45), of Keppo, Kim, Zhang, *Learning Manipulation Through Information
Dissemination* (SSRN 3465030, 2021-09-04): for a normal prior `N(μ, s)` and the Gaussian signal of
(1), the posterior is `N((μ + s Z^q)/(1 + s q), s/(1 + s q))`, and unconditional on the signal the
posterior mean is `N(μ, s² q/(1 + s q))`.

**Formalization Note.** "`q ∈ ℝ`" is read as `q ∈ ℝ₊`, the model's own range. `Z^q` is the scalar
terminal signal, as in (2). `s = 0` and `q = 0` are included, as Dirac masses. -/
theorem lemma_EC_2 (μ : ℝ) (s q : ℝ≥0) :
    (∀ᵐ z ∂(signalKernel q ∘ₘ gaussianReal μ s),
      (posterior (signalKernel q) (gaussianReal μ s)) z =
        gaussianReal ((μ + s * z) / (1 + s * q)) (postVar s q)) ∧
    (∀ᵐ z ∂(signalKernel q ∘ₘ gaussianReal μ s),
      ∫ θ, θ ∂(posterior (signalKernel q) (gaussianReal μ s)) z = (μ + s * z) / (1 + s * q) ∧
      Var[fun θ : ℝ => θ; (posterior (signalKernel q) (gaussianReal μ s)) z] = postVar s q) ∧
    (signalKernel q ∘ₘ gaussianReal μ s).map (fun z : ℝ => (μ + s * z) / (1 + s * q)) =
      gaussianReal μ (meanVar s q) := by sorry

end LearnManip
