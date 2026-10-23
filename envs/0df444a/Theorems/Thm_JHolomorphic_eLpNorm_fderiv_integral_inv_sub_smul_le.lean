-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_fderiv_integral_inv_sub_smul_le
-- name    : JHolomorphic.eLpNorm_fderiv_integral_inv_sub_smul_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T09:08:14.92803+00:00
-- url     : https://prove2.me/theorems/cc4e29c3-8806-4d42-a93b-897cf784fe29
-- title:
--   A local $L^p$ bound for the derivatives of the Cauchy transform of smooth data
-- statement:
--   Let $E$ be a finite-dimensional complex normed space, $2<p<\infty$ and $R>0$. There is a constant $M\ge0$ such that for every $C^\infty$ map $h:\mathbb C\to E$ with compact support contained in the open disc $B_{2R}(0)$, the Cauchy transform
--   $$w(z)=\int_{\mathbb C}\frac{h(\zeta)}{z-\zeta}\,d\zeta$$
--   satisfies
--   $$\|\partial_sw\|_{L^p(B_R(0))}+\|\partial_tw\|_{L^p(B_R(0))}\le M\,\|h\|_{L^p(\mathbb C)}\qquad(z=s+it).$$
--   This is the local $W^{1,p}$ bound for the Cauchy transform of smooth data, with a constant independent of $h$.
--
--   **Formalization Note** $w$ is `fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ`; $\partial_sw$, $\partial_tw$ are `fderiv ℝ w z 1`, `fderiv ℝ w z Complex.I`. The hypotheses are `ContDiff ℝ ∞ h`, `HasCompactSupport h`, `Function.support h ⊆ ball 0 (2 * R)`, and the conclusion is stated with `eLpNorm` on `volume.restrict (ball 0 R)` and `ENNReal.ofReal M * eLpNorm h (ENNReal.ofReal p) volume`.
-- source:
--   Standard estimate for the Cauchy transform; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Lemma 2.24

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- Let `E` be a finite-dimensional complex normed space, `2 < p < ∞` and `R > 0`. There is
`M ≥ 0` such that for every smooth `h : ℂ → E` with compact support in the disc `B_{2R}(0)`, the
map `w(z) = ∫ (z - ζ)⁻¹ h(ζ) dζ` satisfies `‖∂ₛw‖_{L^p(B_R)} + ‖∂ₜw‖_{L^p(B_R)} ≤ M ‖h‖_{L^p}`. -/
theorem eLpNorm_fderiv_integral_inv_sub_smul_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (p R : ℝ) (hp : 2 < p) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℂ → E, ContDiff ℝ ∞ h → HasCompactSupport h →
      Function.support h ⊆ ball 0 (2 * R) →
      eLpNorm (fun z => fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z 1) (ENNReal.ofReal p)
          (volume.restrict (ball 0 R)) +
        eLpNorm (fun z => fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z Complex.I) (ENNReal.ofReal p)
          (volume.restrict (ball 0 R)) ≤
        ENNReal.ofReal M * eLpNorm h (ENNReal.ofReal p) volume := by
  sorry

end JHolomorphic
