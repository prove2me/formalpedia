-- Prove2me | Theorems.Thm_MellinConvolutionTransform
-- name    : MellinConvolutionTransform
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:34:11.868975+00:00
-- url     : https://prove2.me/theorems/7ed4b175-4b88-4233-a006-83e8a4c23e61
-- title:
--   Mellin convolution theorem: $\mathcal{M}(f\ast g)(s)=\mathcal{M}f(s)\,\mathcal{M}g(s)$
-- statement:
--   Let $f,g\colon\mathbb{R}\to\mathbb{C}$ and let $s\in\mathbb{C}$. Assume the joint integrability hypothesis that the function
--
--   $$(x,y)\;\longmapsto\; f(y)\,g\!\left(\frac{x}{y}\right)\frac{1}{y}\,x^{s-1}$$
--
--   is integrable on the product $(0,\infty)\times(0,\infty)$. Then the Mellin transform of the multiplicative convolution $(f\ast g)(x)=\int_0^\infty f(y)g(x/y)\,dy/y$ factors:
--
--   $$\mathcal{M}(f\ast g)(s) \;=\; \mathcal{M}f(s)\cdot \mathcal{M}g(s),$$
--
--   where $\mathcal{M}h(s)=\int_0^{\infty} h(x)\,x^{s-1}\,dx$ denotes the Mellin transform.
--
--   This is the multiplicative-group analogue of the classical convolution theorem for the Fourier transform: convolution against the Haar measure $dy/y$ on $(0,\infty)$ becomes pointwise multiplication on the Mellin side. The single Fubini-ready integrability hypothesis on the double integrand is exactly what the proof's interchange of integrals requires.
--
--   In the PNT development it is the identity that converts the smoothed cutoff $\widetilde{1_\varepsilon}=\mathbf{1}_{(0,1]}\ast \nu_\varepsilon$ into the product formula $\mathcal{M}(\widetilde{1_\varepsilon})(s)=\frac1s\,\mathcal{M}\nu(\varepsilon s)$, the key analytic handle on the mollified Perron integrand.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L285-L325

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

-- TODO: generalize to `RCLike`

local notation (name := mellintransform) "𝓜" => mellin
set_option backward.isDefEq.respectTransparency false

theorem MellinConvolutionTransform (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun x y ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)).uncurry
      (Ioi 0 ×ˢ Ioi 0)) :
    𝓜 (MellinConvolution f g) s = 𝓜 f s * 𝓜 g s := by sorry
