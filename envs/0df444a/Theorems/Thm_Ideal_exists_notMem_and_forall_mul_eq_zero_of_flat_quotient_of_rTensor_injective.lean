-- Prove2me | Theorems.Thm_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective
-- name    : Ideal.exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/9d3fc0e2-471d-5181-852d-d1073606b36e
-- title:
--   Nakayama: finitely generated ideal with flat quotient dies near 𝔭
-- statement:
--   Let $R$, $A$ be commutative rings with $A$ an $R$-algebra, and let $K$ be a field that is also an $R$-algebra (all three in the same universe). Let $J$ be an ideal of $A$ which is finitely generated (`J.FG`) and such that the quotient $A/J$ is flat as an $R$-module. Let $\mathfrak p$ be a prime ideal of $A$, and assume that the kernel of the structure map $R \to K$ is exactly the contraction $\mathfrak q = \mathfrak p \cap R$, i.e. the preimage of $\mathfrak p$ under $R \to A$. Assume finally that the $R$-linear map obtained from the quotient algebra map $A \to A/J$ by tensoring with $K$ on the right, $A \otimes_R K \to (A/J) \otimes_R K$, is injective. Then there is an element $s \in A$ with $s \notin \mathfrak p$ such that $s j = 0$ for every $j \in J$; that is, $J$ is annihilated by a single element not in $\mathfrak p$, so $J$ vanishes on a neighbourhood of $\mathfrak p$ in $\operatorname{Spec} A$.
--
--   This is the commutative-algebra core of the statement that a closed subscheme whose complementary quotient is flat over the base and which is empty over a point spreads out to being empty over a neighbourhood of that point: an ideal-theoretic Nakayama argument over the local ring at $\mathfrak p$. It is used in the scheme-theoretic lemma [`AlgebraicGeometry.exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField`](thm.html#AlgebraicGeometry.exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField), where a closed immersion that is an isomorphism over the residue field of a point is shown to be an isomorphism over an affine neighbourhood.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Ideal.exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective
    {R A K : Type u} [CommRing R] [CommRing A] [Algebra R A] [Field K] [Algebra R K]
    (J : Ideal A) (hJ : J.FG) [Module.Flat R (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hK : RingHom.ker (algebraMap R K) = 𝔭.comap (algebraMap R A))
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ R J).toLinearMap.rTensor K)) :
    ∃ s : A, s ∉ 𝔭 ∧ ∀ j ∈ J, s * j = 0 := by sorry
