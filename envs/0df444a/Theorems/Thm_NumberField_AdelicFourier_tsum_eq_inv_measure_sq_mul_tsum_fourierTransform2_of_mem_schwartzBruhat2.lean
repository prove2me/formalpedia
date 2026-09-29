-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
-- name    : NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/182e2817-3c9c-58f1-9520-55cf3d7b710f
-- title:
--   Adelic Poisson summation in two variables
-- statement:
--   Let $F$ be a number field with adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, equipped with a measurable structure that is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $\mathbb{A}_F$. Let $\psi$ be an additive character $\mathbb{A}_F \to \mathbb{C}^\times$ which is a global additive character in the sense of `IsGlobalAddChar`: it is trivial on the image of $F$ under the structure map $F \to \mathbb{A}_F$, it is continuous, and it is not the trivial character. Let $\Phi : \mathbb{A}_F^2 \to \mathbb{C}$ (functions on `Fin 2 → AdeleRing (𝓞 F) F`) lie in `schwartzBruhat2 F`, the $\mathbb{C}$-linear span of the pure tensors $x \mapsto g\bigl((\text{ringEquiv\_mixedSpace}(x_i)_\infty)_i\bigr)\, h\bigl(((x_i)_{\mathrm{fin}})_i\bigr)$ with $g$ a Schwartz function on the square of the mixed space of $F$ and $h$ a locally constant, compactly supported function on the square of the finite adele ring. Write $\widehat{\Phi} =$ `fourierTransform2 ψ μ Φ` for the integral $w \mapsto \int_{\mathbb{A}_F^2} \psi\bigl(-(v_0 w_0 + v_1 w_1)\bigr)\Phi(v)\, d(\mu \otimes \mu)(v)$, and let `adelicBox F` be the set of adeles whose infinite part lies in the preimage under `ringEquiv_mixedSpace` of the fundamental domain of the $\mathbb{Z}$-span of `mixedEmbedding.latticeBasis F` and whose finite part is integral at every finite place. Then the family $\xi \mapsto \Phi(\xi_0, \xi_1)$, indexed by $\xi \in F^2$ mapped into $\mathbb{A}_F^2$ coordinatewise, is summable, the corresponding family for $\widehat{\Phi}$ is summable, and $$\sum_{\xi \in F^2} \Phi(\xi) = \bigl(\mu(\text{adelicBox } F)^2\bigr)^{-1} \sum_{\xi \in F^2} \widehat{\Phi}(\xi),$$ the measure of the box being taken as a real number and then viewed in $\mathbb{C}$.
--
--   This is the Poisson summation formula for the lattice $F^2 \subset \mathbb{A}_F^2$ applied to Schwartz–Bruhat functions of two adelic variables, with the covolume factor recorded explicitly rather than by normalising $\mu$ so that the adelic box has measure one. It is the analytic input for the transformation law of the adelic theta series $\Theta_\Phi(t,g) = \sum_{\xi \in F^2} \Phi(t\xi g)$ under $g \mapsto {}^t g^{-1}$, and is cited by [`NumberField.AdelicFourier.tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2`](thm.html#NumberField.AdelicFourier.tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2) and by the summation identity over the centraliser in the Godement section construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm

theorem NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    Summable (fun ξ : Fin 2 → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    Summable (fun ξ : Fin 2 → F =>
      fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    ∑' ξ : Fin 2 → F, Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
      = (((μ (adelicBox F)).toReal : ℂ) ^ 2)⁻¹ *
          ∑' ξ : Fin 2 → F, fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by sorry
