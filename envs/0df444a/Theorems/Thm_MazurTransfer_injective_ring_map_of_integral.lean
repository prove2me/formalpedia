-- Prove2me | Theorems.Thm_MazurTransfer_injective_ring_map_of_integral
-- name    : MazurTransfer.injective_ring_map_of_integral
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T14:36:11.370744+00:00
-- url     : https://prove2.me/theorems/3ab6043b-3f30-41a0-a7bd-c362a92ed5ae
-- title:
--   Injectivity on the coefficient ring detects injectivity of a map from an integral domain
-- statement:
--   For an integral domain A integral over a nontrivial commutative ring R, a ring homomorphism f from A is injective whenever its restriction to R is injective. Its kernel has zero contraction, hence is zero by integrality. The downstream consumer extends the literal order-thirteen diamond coordinate substitution to the actual curve function field.
-- source:
--   Owned MazurTheorem integration lemma using Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474; Apache-2.0.

import Mathlib
universe u v w

theorem MazurTransfer.injective_ring_map_of_integral (R : Type u) [CommRing R] [Nontrivial R]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra R A] [Algebra.IsIntegral R A]
    (B : Type w) [CommRing B] (f : A →+* B)
    (h : Function.Injective (f.comp (algebraMap R A))) : Function.Injective f := by sorry
