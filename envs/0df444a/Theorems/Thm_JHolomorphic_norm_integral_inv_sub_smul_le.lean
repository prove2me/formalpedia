-- Prove2me | Theorems.Thm_JHolomorphic_norm_integral_inv_sub_smul_le
-- name    : JHolomorphic.norm_integral_inv_sub_smul_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T08:45:04.869994+00:00
-- url     : https://prove2.me/theorems/eb72e6d9-153a-4d10-aa28-3244c2ae29e8
-- title:
--   A uniform bound for the Cauchy transform of compactly supported $L^p$ data, $p>2$
-- statement:
--   Let $2<p<\infty$, $R>0$ and let $E$ be a complex normed space. There is a constant $C\ge0$ such that for every $g\in L^p(\mathbb C;E)$ vanishing outside the open disc $B_R(0)$ and every $z\in B_R(0)$, the map $\zeta\mapsto(z-\zeta)^{-1}g(\zeta)$ is Lebesgue integrable on $\mathbb C$ and
--   $$\Big\|\int_{\mathbb C}\frac{g(\zeta)}{z-\zeta}\,d\zeta\Big\|\le C\,\|g\|_{L^p(\mathbb C)}.$$
--   This is the uniform bound for the Cauchy transform of compactly supported $L^p$ data, $p>2$, used to build local solutions of Cauchy–Riemann type equations.
--
--   **Formalization Note** $g:\mathbb C\to E$ with `MemLp g (ENNReal.ofReal p) volume` and `Function.support g ⊆ ball 0 R`; the integrand is `(z - ζ)⁻¹ • g ζ` (complex scalar multiplication), and the bound is `‖∫ ζ, (z - ζ)⁻¹ • g ζ‖ ≤ C * (eLpNorm g (ENNReal.ofReal p) volume).toReal`.
-- source:
--   Standard estimate for the Cauchy transform; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Lemma 2.24

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- Let `2 < p < ∞` and `R > 0`. There is `C ≥ 0` such that for every `g ∈ L^p(ℂ; E)` vanishing
outside the disc `B_R(0)` and every `z ∈ B_R(0)`, the map `ζ ↦ (z - ζ)⁻¹ g(ζ)` is integrable and
`‖∫ (z - ζ)⁻¹ g(ζ) dζ‖ ≤ C ‖g‖_{L^p}`. -/
theorem norm_integral_inv_sub_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p R : ℝ) (hp : 2 < p) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, MemLp g (ENNReal.ofReal p) volume →
      Function.support g ⊆ ball 0 R → ∀ z ∈ ball (0 : ℂ) R,
        Integrable (fun ζ => (z - ζ)⁻¹ • g ζ) ∧
        ‖∫ ζ, (z - ζ)⁻¹ • g ζ‖ ≤ C * (eLpNorm g (ENNReal.ofReal p) volume).toReal := by
  sorry

end JHolomorphic
