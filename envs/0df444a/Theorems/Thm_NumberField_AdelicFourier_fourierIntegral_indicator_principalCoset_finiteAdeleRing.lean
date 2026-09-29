-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing
-- name    : NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/f8d567e8-8a0a-5221-831e-e936f986ad25
-- title:
--   Finite-adelic Fourier transform of a principal-coset indicator
-- statement:
--   Let $F$ be a number field, and equip the finite adele ring $\mathbb{A}_F^f =$ `FiniteAdeleRing (𝓞 F) F` with a measurable space structure that is the Borel structure of its topology. Let $\nu$ be an additive Haar measure on $\mathbb{A}_F^f$, and let $\psi_f$ be a continuous additive character $\mathbb{A}_F^f \to \mathbb{C}$. Let $d \in \mathcal{O}_F$ be nonzero and let $k, \xi \in F$, and write $\iota$ for the canonical map $F \to \mathbb{A}_F^f$. Put $\widehat{\mathcal{O}}_F = \{x \in \mathbb{A}_F^f : x_v \in \mathcal{O}_v \text{ for every } v \in \mathrm{Spec}^1(\mathcal{O}_F)\}$, the set of finite adeles integral at every height-one prime, and let $S$ be the image of $\widehat{\mathcal{O}}_F$ under $z \mapsto \iota(k) + \iota(d) z$. Then the Fourier integral $\int_{\mathbb{A}_F^f} \psi_f(-(z \cdot \iota\xi)) \mathbf{1}_S(z)\, d\nu(z)$ equals $\psi_f(-\iota(k\xi))$ times the complex number obtained from the real number $\nu(S)$, times $1$ if $\psi_f(\iota(d\xi) z) = 1$ for every $z \in \widehat{\mathcal{O}}_F$, and times $0$ otherwise. Here $\mathbf 1_S$ is the $\mathbb{C}$-valued indicator of $S$.
--
--   This is the standard local-to-global computation of the Fourier transform of the characteristic function of an affine coset $k + d\,\widehat{\mathcal{O}}_F$ of finite adeles, evaluated at a point coming from $F$: the translation contributes the phase $\psi_f(-\iota(k\xi))$, Haar invariance contributes the mass $\nu(S)$, and character orthogonality on $\widehat{\mathcal{O}}_F$ contributes the conductor condition that $\psi_f$ be trivial on $\iota(d\xi)\widehat{\mathcal{O}}_F$. It feeds the adelic Poisson-summation identities used in the project, namely [`NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi`](thm.html#NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi) and [`NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace`](thm.html#NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Algebra.Module.ZLattice.Covolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
open scoped Classical in

theorem NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k ξ : F) :
    fourierIntegral ψf ν
        (((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator 1)
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)
      = ψf (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k * ξ)))
        * ((ν ((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
              ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * z) = 1
            then 1 else 0) := by sorry
