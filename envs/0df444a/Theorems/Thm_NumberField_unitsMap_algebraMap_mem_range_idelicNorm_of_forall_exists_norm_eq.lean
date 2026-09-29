-- Prove2me | Theorems.Thm_NumberField_unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq
-- name    : NumberField.unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/404e7896-bdc2-5a02-b2b7-b42e61001d7a
-- title:
--   Everywhere-local norms give an idelic norm
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra that is finite-dimensional and Galois over $E$, and let $a$ be a unit of $E$. Assume: (i) for every height-one prime $w$ of the ring of integers $\mathcal{O}_E$ there is an element $z$ of the $E_w$-algebra $E_w \otimes_E M$, where $E_w$ denotes the adic completion of $E$ at $w$, whose algebra norm over $E_w$ is the image of $a$ under $E \to E_w$; and (ii) there is an element $z$ of $\mathbb{A}_{E,\infty} \otimes_E M$, with $\mathbb{A}_{E,\infty}$ the infinite adele ring of $E$, whose algebra norm over $\mathbb{A}_{E,\infty}$ is the image of $a$ under $E \to \mathbb{A}_{E,\infty}$. Then the principal idele attached to $a$, i.e. the image of $a$ under the map of unit groups induced by $E \to \mathbb{A}_E :=$ `AdeleRing (𝓞 E) E`, lies in the range of `idelicNorm` of `genuineBaseChange E M`: the homomorphism $\mathbb{A}_M^\times \to \mathbb{A}_E^\times$ obtained by applying `Units.map` to the algebra norm of $\mathbb{A}_M$ over $\mathbb{A}_E$, taken for the $\mathbb{A}_E$-algebra structure on $\mathbb{A}_M$ given by the ring homomorphism `genuineβ E M`, which is compatible with the maps from $E$ and $M$ and for which base change provides an $\mathbb{A}_E$-algebra isomorphism $\mathbb{A}_E \otimes_E M \cong \mathbb{A}_M$ sending $1 \otimes m$ to the image of $m$.
--
--   This is the passage from everywhere-local (semi-local) norms to global idelic norms, the shape in which the local hypotheses of Hasse's norm theorem are used. It is invoked in the automorphic-forms part of the development, in the lemmas [`AutomorphicForm.exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime`](thm.html#AutomorphicForm.exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime), [`AutomorphicForm.exists_finset_not_isNormOf_and_not_card_eq_one_of_ratio_not_mem_range_norm_of_prime`](thm.html#AutomorphicForm.exists_finset_not_isNormOf_and_not_card_eq_one_of_ratio_not_mem_range_norm_of_prime) and [`AutomorphicForm.isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf`](thm.html#AutomorphicForm.isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq.lean

import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem NumberField.unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (a : Eˣ)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 E), ∃ z : w.adicCompletion E ⊗[E] M,
      Algebra.norm (w.adicCompletion E) z = algebraMap E (w.adicCompletion E) (a : E))
    (hinf : ∃ z : InfiniteAdeleRing E ⊗[E] M,
      Algebra.norm (InfiniteAdeleRing E) z = algebraMap E (InfiniteAdeleRing E) (a : E)) :
    Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) a ∈
      (M4aHerbrand.GenuineDescent.genuineBaseChange E M).idelicNorm.range := by sorry
