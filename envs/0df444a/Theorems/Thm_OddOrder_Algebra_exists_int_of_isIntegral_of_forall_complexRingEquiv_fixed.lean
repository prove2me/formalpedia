-- Prove2me | Theorems.Thm_OddOrder_Algebra_exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed
-- name    : OddOrder.Algebra.exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:06:53.237203+00:00
-- url     : https://prove2.me/theorems/a15d9f9f-d8f4-4103-a01f-9491605fc36e
-- title:
--   An algebraic integer fixed by all ring automorphisms of $\mathbb{C}$ is a rational integer (Isaacs 3.14, core)
-- statement:
--   Let $\alpha\in\mathbb{C}$ be integral over $\mathbb{Z}$, and suppose $\sigma(\alpha)=\alpha$ for every ring automorphism $\sigma:\mathbb{C}\to\mathbb{C}$ (not necessarily continuous). Then $\alpha$ is a rational integer:
--   $$\exists z\in\mathbb{Z},\quad (z:\mathbb{C})=\alpha.$$
--
--   This is the arithmetic core of Isaacs' Lemma 3.14 (and Peterfalvi (13.9.b)). It is used to show that sums of products of character values over Galois-stable sets are rational integers.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Algebra/GaloisRationalInteger.lean#L65-L105

import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclotomicGaloisAction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Definitions.Def_OddOrder_Algebra_GaloisRationalInteger
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

namespace OddOrder.Algebra

open Polynomial IntermediateField

theorem exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed {α : ℂ}
    (hα : IsIntegral ℤ α) (hfix : ∀ σ : ℂ ≃+* ℂ, σ α = α) :
    ∃ z : ℤ, (z : ℂ) = α := by sorry

end OddOrder.Algebra
