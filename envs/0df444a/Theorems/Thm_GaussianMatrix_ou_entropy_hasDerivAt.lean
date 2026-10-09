-- Prove2me | Theorems.Thm_GaussianMatrix_ou_entropy_hasDerivAt
-- name    : GaussianMatrix.ou_entropy_hasDerivAt
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:08:03.936477+00:00
-- url     : https://prove2.me/theorems/c4907cc8-97a8-41e9-9e2e-0c2371cac042
-- title:
--   Entropy dissipation along the Ornstein–Uhlenbeck semigroup: $\frac{d}{dt}\int P_tf\log P_tf\,d\gamma=-\int ((P_tf)')^2/P_tf\,d\gamma$
-- statement:
--   Let $\gamma=N(0,1)$ be the standard Gaussian measure on $\mathbb{R}$. For $s\in\mathbb{R}$ and a function $h$, let
--   $$P_sh(x)=\int h\big(e^{-s}x+\sqrt{1-e^{-2s}}\,y\big)\,d\gamma(y)$$
--   be the Ornstein–Uhlenbeck (Mehler) semigroup. Let $\delta>0$ and $C\in\mathbb{R}$, and let $f\in C^1(\mathbb{R})$ satisfy $\delta\le f\le C$ and $|f'|\le C$. Then for every $t>0$ the function $s\mapsto\int P_sf\log P_sf\,d\gamma$ is differentiable at $t$, and
--   $$\frac{d}{ds}\Big|_{s=t}\int P_sf\log P_sf\,d\gamma\;=\;-\int\frac{\big((P_tf)'\big)^2}{P_tf}\,d\gamma ,$$
--   where $(P_tf)'$ is the derivative of $x\mapsto P_tf(x)$.
--
--   This is the de Bruijn-type identity behind the Bakry–Émery proof of the Gaussian log-Sobolev inequality: the entropy decreases with rate equal to the Fisher information. The proof has three ingredients:
--   - differentiation under the integral sign;
--   - the generator identity $\partial_tP_tf=(P_tf)''-x(P_tf)'$, valid for $t>0$ even though only $f\in C^1$ is assumed, because Gaussian integration by parts in the noise variable gives $(P_tf)''=\frac{e^{-2t}}{\sqrt{1-e^{-2t}}}\int y\,f'(e^{-t}x+\sqrt{1-e^{-2t}}\,y)\,d\gamma(y)$;
--   - Gaussian integration by parts in $x$.
--
--   **Formalization Note.** $P_sf$ is written out explicitly. The restriction $t>0$ is needed, since $\sqrt{1-e^{-2s}}$ is not differentiable at $s=0$.
-- source:
--   D. Bakry, I. Gentil, M. Ledoux, Analysis and Geometry of Markov Diffusion Operators (Springer, 2014), §2.7.1 (Ornstein–Uhlenbeck semigroup, Mehler formula) and §5.7 (entropy dissipation $\frac{d}{dt}\mathrm{Ent}(P_tf)=-I(P_tf)$); M. Ledoux, The Concentration of Measure Phenomenon (AMS, 2001), §5.1 (proof of Theorem 5.1). Section numbers are cited from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem ou_entropy_hasDerivAt (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (δ C : ℝ) (hδ : 0 < δ)
    (hlow : ∀ x, δ ≤ f x) (hup : ∀ x, f x ≤ C) (hdf : ∀ x, |deriv f x| ≤ C) (t : ℝ)
    (ht : 0 < t) :
    HasDerivAt
      (fun s => ∫ x,
        (∫ y, f (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-(2 * s))) * y) ∂(gaussianReal 0 1))
          * Real.log (∫ y, f (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-(2 * s))) * y)
              ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1))
      (-∫ x,
        deriv (fun z => ∫ y, f (Real.exp (-t) * z + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
            ∂(gaussianReal 0 1)) x ^ 2
          / ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y) ∂(gaussianReal 0 1)
        ∂(gaussianReal 0 1)) t := by
  sorry

end GaussianMatrix
