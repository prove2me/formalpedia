-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi
-- name    : NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/7db87906-aa89-539d-bf85-fa9aa43c7422
-- title:
--   Adelic Poisson summation for Schwartz times box indicator
-- statement:
--   Let $F$ be a number field, equip its adele ring $\mathbb{A}_F=\mathbb{A}_{F,\infty}\times\mathbb{A}_{F,\mathrm{f}}$ with a measurable structure that is Borel for its topology, and let $\mu$ be an additive Haar measure on $\mathbb{A}_F$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ satisfying the project's predicate `IsGlobalAddChar`: $\psi$ is trivial on the image of $F$, continuous, and not identically $1$. Let $g$ be a Schwartz function on two copies of the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of $F$, let $d\in\mathcal{O}_F$ be nonzero, and let $k=(k_0,k_1)\in F^2$. Assume $\Phi:(\mathbb{A}_F)^2\to\mathbb{C}$ is the function sending $x$ to $g$ evaluated at the infinite components of $x_0,x_1$ transported to the mixed space by `InfiniteAdeleRing.ringEquiv_mixedSpace`, multiplied by the indicator of the product over $i\in\{0,1\}$ of the image of $\{z : z_v\in\mathcal{O}_v \text{ for all } v\}$ under $z\mapsto k_i+dz$, evaluated at the finite components of $x_0,x_1$. Then both $\xi\mapsto\Phi(\xi)$ and $\xi\mapsto\widehat{\Phi}(\xi)$ are summable over $\xi\in F^2$ (embedded diagonally), and $\sum_{\xi\in F^2}\Phi(\xi)=\big((\mu(B))^{2}\big)^{-1}\sum_{\xi\in F^2}\widehat{\Phi}(\xi)$, where $\widehat{\Phi}(w)=\int \psi(-(v_0w_0+v_1w_1))\Phi(v)\,d(\mu\otimes\mu)(v)$ and $B$ is the adelic box: infinite part in the preimage of the fundamental domain of the lattice basis of $F$, finite part integral at every place.
--
--   This is Poisson summation on the adelic plane in the basic case where the finite-adelic factor is the indicator of a translate $k+d\widehat{\mathcal{O}}$ in each variable, the self-dual volume constant appearing as $\mu(B)^{-2}$. It is the computational core from which the summation formula for a general Schwartz–Bruhat function of two adelic variables is obtained by linearity, and is cited in that form by [`NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2`](thm.html#NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain

open scoped Classical in

theorem NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (g : SchwartzMap (Fin 2 → mixedEmbedding.mixedSpace F) ℂ) (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ = fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
      * (Set.pi Set.univ fun i => (fun z : FiniteAdeleRing (𝓞 F) F ↦
            algebraMap F (FiniteAdeleRing (𝓞 F) F) (k i)
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2)) :
    Summable (fun ξ : Fin 2 → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    Summable (fun ξ : Fin 2 → F =>
      fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    ∑' ξ : Fin 2 → F, Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
      = (((μ (adelicBox F)).toReal : ℂ) ^ 2)⁻¹ *
          ∑' ξ : Fin 2 → F, fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by sorry
