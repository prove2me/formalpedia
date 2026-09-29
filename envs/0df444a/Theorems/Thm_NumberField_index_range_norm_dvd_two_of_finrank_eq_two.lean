-- Prove2me | Theorems.Thm_NumberField_index_range_norm_dvd_two_of_finrank_eq_two
-- name    : NumberField.index_range_norm_dvd_two_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/a1aea64b-4d05-5b3a-9d23-fcfbfb594057
-- title:
--   Local norm index divides 2 in a quadratic extension
-- statement:
--   Let $K$ and $L$ be number fields, with $L$ a $K$-algebra such that $\dim_K L = 2$. Two assertions are made simultaneously. First, for every height-one prime $v$ of the ring of integers $\mathcal{O}_K$, let $K_v$ denote the $v$-adic completion of $K$ and form the $K_v$-algebra $L \otimes_K K_v$ (the tensor product being regarded as a $K_v$-algebra through the right factor); then the image of the unit group $(L \otimes_K K_v)^\times$ under the homomorphism induced on units by the algebra norm $\mathrm{N}_{(L \otimes_K K_v)/K_v}$ is a subgroup of $K_v^\times$ whose index divides $2$. Second, for every infinite place $w$ of $K$, with $K_w$ the completion of $K$ at $w$, the image of $(L \otimes_K K_w)^\times$ under the homomorphism induced on units by the algebra norm $\mathrm{N}_{(L \otimes_K K_w)/K_w}$ is a subgroup of $K_w^\times$ whose index divides $2$. In particular each of these local norm groups has index $1$ or $2$; note that divisibility of the index by $2$ is asserted in the sense of natural numbers, so in particular each index is finite.
--
--   This is the local norm index theorem for a quadratic extension of number fields: at every place, finite or infinite, the group of local norms from the semilocal algebra $L \otimes_K K_v$ has index dividing the degree $2$. It feeds the global counting statement [`NumberField.finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two`](thm.html#NumberField.finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two), which records that the set of places where a given element fails to be a local norm is finite of even cardinality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_index_range_norm_dvd_two_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.index_range_norm_dvd_two_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (Units.map (Algebra.norm (v.adicCompletion K) :
          L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range.index ∣ 2) ∧
    (∀ w : InfinitePlace K,
      (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range.index ∣ 2) := by sorry
