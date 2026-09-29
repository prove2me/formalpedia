-- Prove2me | Theorems.Thm_NumberField_finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two
-- name    : NumberField.finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/f0dcb2ef-3233-50a7-8bfc-aae8f6a22ade
-- title:
--   Even number of places where a fails to be a local norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, and let $a \in K^\times$. For a nonzero prime $v$ of the ring of integers $\mathcal{O}_K$ (a point of the height-one spectrum), with $v$-adic completion $K_v$, consider the condition that the image of $a$ under $K \to K_v$ does not lie in the set of values $\operatorname{N}_{(L \otimes_K K_v)/K_v}(x)$ taken as $x$ runs over the units of the $K_v$-algebra $L \otimes_K K_v$; and for an infinite place $w$ of $K$, with completion $K_w$, the analogous condition that the image of $a$ in $K_w$ is not the $K_w$-algebra norm of a unit of $L \otimes_K K_w$. The assertion is that the set of such finite places $v$ is finite, and that the sum of its cardinality and the cardinality of the corresponding set of infinite places $w$ is even.
--
--   This is the reciprocity law of class field theory for a quadratic extension in the form of Hilbert's product formula for the quadratic norm residue symbols: an element of $K^\times$ fails to be a local norm from $L$ at only finitely many, and at an even number of, places of $K$. It is used for the variant in which the local norm defect is counted at places in a prescribed set of prime order, and in the study of $\sigma$-conjugacy of scalars for automorphic forms under quadratic base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (a : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | algebraMap K (v.adicCompletion K) (a : K) ∉
        Set.range (fun x : (L ⊗[K] v.adicCompletion K)ˣ =>
          Algebra.norm (v.adicCompletion K) (x : L ⊗[K] v.adicCompletion K))}.Finite ∧
    Even ({v : HeightOneSpectrum (𝓞 K) | algebraMap K (v.adicCompletion K) (a : K) ∉
        Set.range (fun x : (L ⊗[K] v.adicCompletion K)ˣ =>
          Algebra.norm (v.adicCompletion K) (x : L ⊗[K] v.adicCompletion K))}.ncard +
      {w : InfinitePlace K | algebraMap K w.Completion (a : K) ∉
        Set.range (fun x : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (x : L ⊗[K] w.Completion))}.ncard) := by sorry
