-- Prove2me | Theorems.Thm_JHolomorphic_ae_sub_eq_integral_segment
-- name    : JHolomorphic.ae_sub_eq_integral_segment
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T20:19:37.861178+00:00
-- url     : https://prove2.me/theorems/4fd9d902-59b7-42d1-8e5f-3edf95575022
-- title:
--   Increments of a function along a vector are segment integrals of its directional weak derivative
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $W\subseteq\mathbb{C}$, $a\in\mathbb{C}$, and let $f,G:\mathbb{C}\to E$ be integrable on every compact subset of $W$, with $G$ measurable. Assume $G$ is the weak derivative of $f$ in the direction $a$ on $W$:
--   $$\int_{\mathbb{C}} (D\varphi(z)\,a)\,f(z)\,dz=-\int_{\mathbb{C}}\varphi(z)\,G(z)\,dz$$
--   for every real $C^\infty$ function $\varphi$ with compact support in $W$. If $c\in\mathbb{C}$, $r\in\mathbb{R}$ and $B(c,r+|a|)\subseteq W$, then for almost every $z\in B(c,r)$
--   $$f(z+a)-f(z)=\int_0^1 G(z+ta)\,dt.$$
--   This is the representation of increments of a Sobolev function by its directional weak derivative, used for difference-quotient estimates.
--
--   **Formalization Note** The weak derivative hypothesis is stated with `fderiv ℝ φ z a` and test functions satisfying `ContDiff ℝ ∞ φ`, `HasCompactSupport φ`, `tsupport φ ⊆ W`. Measurability of `G` is `StronglyMeasurable G` on all of $\mathbb{C}$. The integral on the right is the interval integral `∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)`, and "almost every $z\in B(c,r)$" is `∀ᵐ z ∂(volume.restrict (ball c r))`.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, §5.8.2, proof of Theorem 3 (i)

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Let `G` be the weak derivative of `f : ℂ → E` in the direction `a` on `W`: `∫ (Dφ · a) f = -∫ φ G`
for every real `C^∞` function `φ` with compact support in `W`. Assume `f` and `G` are integrable on
compact subsets of `W`, `G` is strongly measurable, and `B(c, r + ‖a‖) ⊆ W`. Then
`f (z + a) - f z = ∫₀¹ G (z + t a) dt` for almost every `z ∈ B(c, r)`. -/
theorem ae_sub_eq_integral_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {W : Set ℂ} {f G : ℂ → E} (a : ℂ)
    (hd : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ∫ z, fderiv ℝ φ z a • f z = -∫ z, φ z • G z)
    (hf : ∀ K ⊆ W, IsCompact K → IntegrableOn f K) (hG : StronglyMeasurable G)
    (hGi : ∀ K ⊆ W, IsCompact K → IntegrableOn G K) (c : ℂ) (r : ℝ)
    (hb : ball c (r + ‖a‖) ⊆ W) :
    ∀ᵐ z ∂(volume.restrict (ball c r)), f (z + a) - f z = ∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a) := by
  sorry

end JHolomorphic
