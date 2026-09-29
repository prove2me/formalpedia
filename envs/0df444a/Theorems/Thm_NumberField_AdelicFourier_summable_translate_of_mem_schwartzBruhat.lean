-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat
-- name    : NumberField.AdelicFourier.summable_translate_of_mem_schwartzBruhat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/1420d9cc-9471-5505-832d-41c0ae260df1
-- title:
--   Summability of Schwartz–Bruhat translates over the principal adeles
-- statement:
--   Let $F$ be a number field (a type `F` carrying a field structure together with the `NumberField` instance), and let $\mathbb{A}_F$ denote `AdeleRing (𝓞 F) F`, the product of the infinite adele ring with the finite adele ring of the ring of integers $\mathcal{O}_F$. Let $f : \mathbb{A}_F \to \mathbb{C}$ be a function belonging to `schwartzBruhat F`, that is, to the $\mathbb{C}$-submodule of all functions $\mathbb{A}_F \to \mathbb{C}$ spanned by `pureTensorSet F`: the set of products $x \mapsto g\big(\text{ringEquiv\_mixedSpace}\,F\,(x_\infty)\big)\cdot h(x_{\mathrm{fin}})$ in which $g$ is a Schwartz function on the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of $F$, transported to the infinite adeles along the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace F`, and $h$ is a locally constant, compactly supported function on the finite adele ring. Let $x \in \mathbb{A}_F$ be arbitrary. The conclusion is that the family indexed by $\xi \in F$ whose $\xi$-th term is $f\big(x + \iota(\xi)\big)$, with $\iota$ the diagonal algebra map $F \to \mathbb{A}_F$, is summable; since the values lie in $\mathbb{C}$, this is absolute summability.
--
--   This is the convergence statement for the geometric side of the adelic Poisson summation formula: the sum $\sum_{\xi \in F} f(x + \iota\xi)$ over the discrete, cocompact subgroup of principal adeles is well defined for every Schwartz–Bruhat $f$ and every base point $x$. It underlies the adelic Poisson summation results [`NumberField.AdelicFourier.tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral`](thm.html#NumberField.AdelicFourier.tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral) and [`NumberField.AdelicFourier.tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero`](thm.html#NumberField.AdelicFourier.tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero), and in turn the approximation of unipotent integrals by theta-like sums in [`AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact`](thm.html#AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact). No value of the sum, and no uniformity in $x$, is asserted here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat.lean

import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier

theorem NumberField.AdelicFourier.summable_translate_of_mem_schwartzBruhat (F : Type) [Field F] [NumberField F]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) (x : AdeleRing (𝓞 F) F) :
    Summable fun ξ : F => f (x + algebraMap F (AdeleRing (𝓞 F) F) ξ) := by sorry
