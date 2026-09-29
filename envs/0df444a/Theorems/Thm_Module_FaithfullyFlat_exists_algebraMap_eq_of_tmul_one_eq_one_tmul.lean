-- Prove2me | Theorems.Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul
-- name    : Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/14a48e2e-fa83-5bb5-9a59-b6a25972da06
-- title:
--   Degree-zero exactness of the Amitsur complex
-- statement:
--   Let $A$ and $B$ be commutative rings and let $B$ be an $A$-algebra which is faithfully flat as an $A$-module. Let $b \in B$ be an element whose two canonical images in $B \otimes_A B$ agree, that is $b \otimes 1 = 1 \otimes b$. The conclusion is that $b$ lies in the image of the structure morphism: there exists $a \in A$ with $\mathrm{algebraMap}\ A\ B\ a = b$. Equivalently, $A \to B \rightrightarrows B \otimes_A B$, with the two parallel maps $b \mapsto b \otimes 1$ and $b \mapsto 1 \otimes b$, is exact at $B$ in the sense that every element equalised by the two maps comes from $A$. Only existence of such an $a$ is asserted; uniqueness (which follows from the injectivity of $A \to B$ for a faithfully flat algebra) is not part of the statement. The two rings may lie in different universes.
--
--   This is the degree-zero exactness of the Amitsur complex, the first and most elementary case of Grothendieck's faithfully flat descent: invariant elements descend. It is used in the project when descending data along a faithfully flat base change, for instance in the construction of corepresenting objects from descent data, in the analysis of comultiplication-compatible elements of Hopf algebras, and in the descent of Katz level-$p$ forms on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open TensorProduct

theorem Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {b : B} (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b := by sorry
