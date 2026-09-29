-- Prove2me | Theorems.Thm_MeasureTheory_setIntegral_integral_swap
-- name    : MeasureTheory.setIntegral_integral_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:33:58.820362+00:00
-- url     : https://prove2.me/theorems/284d29c4-985e-480e-80aa-d379c0c93764
-- title:
--   Fubini–Tonelli swap for iterated integrals over a product of sets
-- statement:
--   Let $(\alpha,\mu)$ and $(\beta,\nu)$ be measurable spaces equipped with $\sigma$-finite measures, let $E$ be a real normed space (a Banach-space-valued Bochner integral setting), and let $f\colon\alpha\to\beta\to E$. Fix sets $s\subseteq\alpha$ and $t\subseteq\beta$, and assume the uncurried function $(x,y)\mapsto f(x)(y)$ is integrable on the product set $s\times t$ with respect to the product measure $\mu\otimes\nu$. Then the two iterated set integrals agree:
--
--   $$\int_{s}\!\left(\int_{t} f(x)(y)\, d\nu(y)\right) d\mu(x) \;=\; \int_{t}\!\left(\int_{s} f(x)(y)\, d\mu(x)\right) d\nu(y).$$
--
--   This is the set-integral form of Fubini's theorem: integrability on the rectangle $s\times t$ for the product measure is exactly the hypothesis needed to interchange the order of integration when both integrals are restricted to sets rather than taken over the whole spaces.
--
--   In this development it is the workhorse behind the Mellin convolution theorem $\mathcal{M}(f\ast g)=\mathcal{M}f\cdot\mathcal{M}g$ and various contour-integral manipulations, where double integrals over $(0,\infty)\times(0,\infty)$ or over rectangle sides must be reordered. It is stated in full generality and is reusable in any Bochner-integration context.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L14-L24

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

theorem MeasureTheory.setIntegral_integral_swap {α : Type*} {β : Type*} {E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    {ν : MeasureTheory.Measure β} [NormedAddCommGroup E]
    [MeasureTheory.SigmaFinite ν] [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ]
    (f : α → β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn (f.uncurry) (s ×ˢ t) (μ.prod ν)) :
    (∫ (x : α) in s, ∫ (y : β) in t, f x y ∂ν ∂μ)
      = ∫ (y : β) in t, ∫ (x : α) in s, f x y ∂μ ∂ν := by sorry
