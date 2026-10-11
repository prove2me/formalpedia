-- Prove2me | Theorems.Thm_MazurTransfer_pic0_subsingleton_of_rational_field_equiv
-- name    : MazurTransfer.pic0_subsingleton_of_rational_field_equiv
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T15:21:27.728902+00:00
-- url     : https://prove2.me/theorems/ef91a46e-57bb-498b-95cf-b7f3835c3620
-- title:
--   The degree-zero arithmetic Picard group of a rational function field is trivial
-- statement:
--   Let K be a field and let F be a field equipped with a K-algebra structure. If e is a K-algebra isomorphism from the rational function field K(t) to F, then the degree-zero arithmetic Picard group Pic0(K,F) has a single element. Every degree-zero divisor is principal: transport it to K(t), use the rational divisor theorem, and transport the principal function back. The named downstream consumer is the actual order-three and hyperelliptic quotient Picard groups of the order-thirteen curve, used to prove that their Galois Picard traces vanish.
-- source:
--   Owned MazurTheorem integration lemma; Apache-2.0. Rational divisor triviality and divisor/Picard transport use https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero.lean and https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_Pic0Congr.lean .

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
universe u v

theorem MazurTransfer.pic0_subsingleton_of_rational_field_equiv (K : Type u) [Field K] (F : Type v) [Field F] [Algebra K F]
    (e : RatFunc K ≃ₐ[K] F) :
    Subsingleton (AlgebraicCurve.Pic0 K F) := by sorry
