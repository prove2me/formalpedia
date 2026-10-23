-- Prove2me | Theorems.Thm_JHolomorphic_exists_weakPartials_integral_inv_sub_smul
-- name    : JHolomorphic.exists_weakPartials_integral_inv_sub_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T09:28:02.158805+00:00
-- url     : https://prove2.me/theorems/369abfe7-ae5d-4373-a506-2e733fe50ce3
-- title:
--   The Cauchy transform of compactly supported $L^p$ data, $p>2$, is a continuous $W^{1,p}$ solution of the Cauchy–Riemann equation
-- statement:
--   Let $E$ be a finite-dimensional complex normed space, $2<p<\infty$, $R>0$, and let $g\in L^p(\mathbb C;E)$ vanish outside the open disc $B_R(0)$. Then the Cauchy transform
--   $$w(z)=\int_{\mathbb C}\frac{g(\zeta)}{z-\zeta}\,d\zeta$$
--   is continuous on $B_R(0)$ and has weak partial derivatives $w_s,w_t\in L^p(B_R(0);E)$ on $B_R(0)$ satisfying
--   $$w_s+i\,w_t=2\pi\,g\qquad\text{almost everywhere on }B_R(0).$$
--   Thus $\frac1{2\pi}w$ is a continuous $W^{1,p}$ solution of $\partial_sw+i\partial_tw=g$ on the disc.
--
--   **Formalization Note** $w$ is `fun z => ∫ ζ, (z - ζ)⁻¹ • g ζ`. The hypotheses are `MemLp g (ENNReal.ofReal p) volume` and `Function.support g ⊆ ball 0 R`. Weak partials are given by `HasWeakPartialsOn (ball 0 R) w ws wt`, `ws` and `wt` lie in `MemLp _ (ENNReal.ofReal p) (volume.restrict (ball 0 R))`, and the equation is `ws z + Complex.I • wt z = (2 * Real.pi : ℂ) • g z` for a.e. `z` in the disc.
-- source:
--   Classical (Cauchy transform, Vekua); used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Lemma 2.24

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- Let `E` be a finite-dimensional complex normed space, `2 < p < ∞`, `R > 0`, and let
`g ∈ L^p(ℂ; E)` vanish outside the disc `B_R(0)`. Then `w(z) = ∫ (z - ζ)⁻¹ g(ζ) dζ` is continuous on
`B_R(0)` and has weak partial derivatives `wₛ`, `wₜ ∈ L^p(B_R(0))` on `B_R(0)` with
`wₛ + i wₜ = 2π g` almost everywhere on `B_R(0)`. -/
theorem exists_weakPartials_integral_inv_sub_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (p R : ℝ) (hp : 2 < p) (hR : 0 < R)
    (g : ℂ → E) (hg : MemLp g (ENNReal.ofReal p) volume)
    (hsupp : Function.support g ⊆ ball 0 R) :
    ContinuousOn (fun z => ∫ ζ, (z - ζ)⁻¹ • g ζ) (ball 0 R) ∧
      ∃ ws wt : ℂ → E, HasWeakPartialsOn (ball 0 R) (fun z => ∫ ζ, (z - ζ)⁻¹ • g ζ) ws wt ∧
        MemLp ws (ENNReal.ofReal p) (volume.restrict (ball 0 R)) ∧
        MemLp wt (ENNReal.ofReal p) (volume.restrict (ball 0 R)) ∧
        ∀ᵐ z ∂(volume.restrict (ball 0 R)), ws z + Complex.I • wt z = (2 * Real.pi : ℂ) • g z := by
  sorry

end JHolomorphic
