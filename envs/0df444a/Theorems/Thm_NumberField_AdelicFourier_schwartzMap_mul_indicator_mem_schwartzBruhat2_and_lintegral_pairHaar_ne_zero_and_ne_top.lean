-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top
-- name    : NumberField.AdelicFourier.schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/9d0bc28b-747d-50a6-a23c-1167f32fce46
-- title:
--   Standard test functions on A_L²: Schwartz–Bruhat, positive finite integral
-- statement:
--   Let $L$ be a number field, let $g$ be a complex-valued Schwartz function on $(\mathrm{Fin}\,2 \to$ mixedSpace$(L))$, i.e. on the square of the mixed archimedean space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of $L$, and assume that $g$ takes real non-negative values (for every $y$, $(g\,y).\mathrm{re}\ge 0$ and $(g\,y).\mathrm{im}=0$) and that $g$ is not identically zero. Let $U$ be a subset of $\mathrm{Fin}\,2\to$ FiniteAdeleRing$(\mathcal{O}_L,L)$ which is open, compact and non-empty, and let $\mu_1$ be an additive Haar measure on the adele ring of $L$, taken with its Borel $\sigma$-algebra. Consider the function $\Phi$ on $\mathrm{Fin}\,2 \to \mathbb{A}_L$ given by $\Phi(x) = g\bigl(i \mapsto \mathrm{ringEquiv\_mixedSpace}\,L\,(x_i)_1\bigr)\cdot \mathbf{1}_U\bigl(i \mapsto (x_i)_2\bigr)$, the product of $g$ evaluated at the archimedean components transported into mixed space with the $\mathbb{C}$-valued indicator of $U$ evaluated at the finite-adelic components. The conclusion is a conjunction of four assertions: $\Phi$ lies in `schwartzBruhat2 L`, the $\mathbb{C}$-span of the functions of the form (Schwartz on the square of mixed space) times (locally constant with compact support on the square of the finite adeles); $\Phi$ takes real non-negative values pointwise; and the lower integral of $x \mapsto \mathrm{ENNReal.ofReal}\,(\Phi(x)).\mathrm{re}$ against `pairHaar` $\mu_1$, the product measure $\mu_1 \otimes \mu_1$ on pairs of adeles, is neither $0$ nor $\infty$, that is $0 < \int \Phi < \infty$.
--
--   This provides the standard test functions $\Phi = g \otimes \mathbf{1}_U$ of two adelic variables used in Godement-type zeta integrals: membership in the Schwartz–Bruhat space, pointwise positivity, and finiteness and non-vanishing of the total integral. It feeds the computation of the behaviour as $s \to 1^+$ of the twisted integral over a centralizer, the factorisation of the integral into an archimedean factor and a finite-adelic factor being supplied by [`NumberField.AdelicBox.lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi`](thm.html#NumberField.AdelicBox.lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

open scoped Classical in

theorem NumberField.AdelicFourier.schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top
    (L : Type) [Field L] [NumberField L]
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ))
    (hg : ∀ y, 0 ≤ (g y).re ∧ (g y).im = 0) (hg0 : ∃ y, g y ≠ 0)
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)) (hUo : IsOpen U) (hUc : IsCompact U) (hUn : U.Nonempty)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] :
    (fun x : Fin 2 → AdeleRing (𝓞 L) L =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)) ∈ schwartzBruhat2 L ∧
    (∀ x : Fin 2 → AdeleRing (𝓞 L) L,
      0 ≤ (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∧
      (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).im = 0) ∧
    (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) ≠ 0 ∧
    (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) ≠ ⊤ := by sorry
