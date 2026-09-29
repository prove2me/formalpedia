-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet
-- name    : NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/cb2cffff-ca2d-5d1c-ab1b-14d163f0246d
-- title:
--   Summability of a pure adelic tensor over principal points
-- statement:
--   Let $F$ be a number field and let $f$ be a complex-valued function on the adele ring $\mathbb{A}_F$ of $F$ (the adele ring of $F$ over its ring of integers $\mathcal{O}_F$) which lies in `pureTensorSet F`; that is, there are a Schwartz function $g$ on the mixed space $\mathrm{mixedSpace}\,F$ of $F$ and a function $h$ on the finite adele ring $\mathbb{A}_{F,\mathrm{fin}}$ which is locally constant and has compact support, such that $f$ factors as $f(x) = g\bigl(\mathrm{ringEquiv\_mixedSpace}_F(x_\infty)\bigr)\cdot h(x_{\mathrm{fin}})$, where $x_\infty$ and $x_{\mathrm{fin}}$ are the infinite and finite components of $x$ and $\mathrm{ringEquiv\_mixedSpace}_F$ is the identification of the infinite adele ring with the mixed space. Then the family indexed by the elements $\xi$ of $F$ whose $\xi$-th term is $f$ evaluated at the image of $\xi$ under the canonical ring map $F \to \mathbb{A}_F$ is summable.
--
--   This is the absolute convergence of the left-hand side of adelic Poisson summation, in the case of a pure tensor of an archimedean Schwartz function with a locally constant compactly supported function on the finite adeles. It is the summability input for the identification of $\sum_{\xi \in F} f(\xi)$ with the corresponding sum of adelic Fourier transforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet.lean

import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier

theorem NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet
    {F : Type*} [Field F] [NumberField F]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    Summable fun ξ : F => f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by sorry
