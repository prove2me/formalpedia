-- Prove2me | Theorems.Thm_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
-- name    : NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/3d52b33a-4f0a-5738-8e5d-b528a02d1313
-- title:
--   Density of 𝒪_F in the integral finite adeles
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and finite adele ring $\mathbb{A}_F^f =$ `FiniteAdeleRing (𝓞 F) F`, the restricted product of the completions $F_v$ with respect to the valuation rings $\mathcal{O}_{F,v}$ over the height-one primes $v$ of $\mathcal{O}_F$, carried with its restricted-product topology. The set `integralFiniteAdeles (𝓞 F) F` is by definition the set of those $x \in \mathbb{A}_F^f$ all of whose components are integral, i.e. $x_v \in \mathcal{O}_{F,v}$ (the subring `v.adicCompletionIntegers F` of `v.adicCompletion F`) for every height-one prime $v$ of $\mathcal{O}_F$. The theorem asserts the inclusion of this set in the topological closure, inside $\mathbb{A}_F^f$, of the image of $\mathcal{O}_F$ under the structure map $\mathcal{O}_F \to \mathbb{A}_F^f$, that is, of the range of `algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)`. In words: every integral finite adele is a limit of diagonally embedded global integers, so $\mathcal{O}_F$ is dense in $\widehat{\mathcal{O}}_F = \prod_v \mathcal{O}_{F,v}$. Only the inclusion is asserted, not the reverse inclusion (equality of the closure with the integral finite adeles).
--
--   This is the finite-place strong approximation statement for the ring of integers: $\mathcal{O}_F$ is dense in its profinite completion $\widehat{\mathcal{O}}_F$ viewed inside $\mathbb{A}_F^f$. It is used in the adelic Fourier-analytic part of the development, where it enters the identification of the annihilator of $\widehat{\mathcal{O}}_F$ under a global additive character with the inverse different, and the construction of a global additive character that is a scalar multiple of the standard one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped Classical nonZeroDivisors

theorem NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
    (F : Type) [Field F] [NumberField F] :
    integralFiniteAdeles (𝓞 F) F
      ⊆ closure (Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F))) := by sorry
