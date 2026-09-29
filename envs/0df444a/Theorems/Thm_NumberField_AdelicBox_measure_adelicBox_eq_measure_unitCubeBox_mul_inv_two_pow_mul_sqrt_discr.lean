-- Prove2me | Theorems.Thm_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr
-- name    : NumberField.AdelicBox.measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/2ecfe15f-f714-5f1a-abee-cb03b3b185fc
-- title:
--   Adelic box has measure 2^{-r₂}√|d_K| times unit cube
-- statement:
--   Let $K$ be a number field, let the adele ring $\mathbb{A}_K = \mathbb{A}_{\mathcal{O}_K,K}$ carry a measurable space structure which is its Borel structure, and let $\mu$ be a measure on $\mathbb{A}_K$ which is assumed to be an additive Haar measure. Write $E$ for the unit cube box: the set of adeles $x$ whose archimedean component $x_1$, transported by the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace` from $K \otimes \mathbb{R}$ to $\prod_{w \text{ real}} \mathbb{R} \times \prod_{w \text{ complex}} \mathbb{C}$, has every real coordinate in $[0,1]$ and every complex coordinate with real part and imaginary part both in $[0,1]$, and whose finite component $x_2$ lies in `integralFiniteAdeles`, i.e. satisfies $x_2(v) \in \mathcal{O}_v$ for every $v$ in the height-one spectrum of $\mathcal{O}_K$. The conclusion is a threefold conjunction: $\mu(E) \neq 0$; $\mu(E) \neq \infty$; and the adelic box `adelicBox K`, namely the set of adeles whose archimedean component is carried by the same isomorphism into the fundamental domain of the $\mathbb{Z}$-span of `mixedEmbedding.latticeBasis K` and whose finite component is integral at every finite place, satisfies $$\mu(\mathrm{adelicBox}\,K) = \mu(E) \cdot \bigl(2^{-1}\bigr)^{r_2(K)} \cdot \mathrm{ofReal}\bigl(\sqrt{|d_K|}\bigr),$$ where $r_2(K)$ is the number of complex places of $K$ and $d_K$ its discriminant, the product being taken in $[0,\infty]$.
--
--   This is the computation of the covolume of $K$ in $\mathbb{A}_K$ in normalisation-free form: for any additive Haar measure, the adelic box (a fundamental domain for the translation action of $K$) has measure $2^{-r_2}\sqrt{|d_K|}$ times that of the unit cube box, so that for the Haar measure giving the unit cube box mass one the covolume is $2^{-r_2}\sqrt{|d_K|}$. It is used in the normalisation of adelic integrals in the automorphic forms part of the development, in the computation of integrals of $\mathrm{GL}_2$ automorphic forms against the idele norm of the determinant and in the associated rate formula involving $\zeta_K(2)$ and the discriminant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr.lean

import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.AdelicBox.measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure) :
    μ {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} ≠ 0 ∧
    μ {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} ≠ ⊤ ∧
    μ (NumberField.AdelicBox.adelicBox K) =
      μ {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} *
        ((2 : ENNReal)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
          ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|)) := by sorry
