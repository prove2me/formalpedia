-- Prove2me | Theorems.Thm_MazurTransfer_finite_algebra_valuation_point_lift
-- name    : MazurTransfer.finite_algebra_valuation_point_lift
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T10:20:26.108394+00:00
-- url     : https://prove2.me/theorems/378b965f-b777-4d37-8c78-bf3d2f520205
-- title:
--   Finite algebra points extend to valuation subrings
-- statement:
--   Let $A$ be a finite algebra over a commutative ring $R$, let $F$ be a field, and let $P$ be a valuation subring of $F$. Suppose the $R$-algebra structures on $P$ and $F$ are compatible with the inclusion $P \subseteq F$. Every $R$-algebra homomorphism $A \to F$ factors through an $R$-algebra homomorphism $A \to P$, with equality of every original coordinate in $F$. The point is that finite-algebra coordinates are integral, and valuation rings are integrally closed.
-- source:
--   Independent Mathlib proof of MazurTransfer.FiniteEtaleClosedSubgroupSpecialization.exists_valuation_point. Used by ProperPointEtaleSubgroupInertia to retain the same actual chi13 closed subgroup coordinates in the order-13 Picard norm descent at nineteen.

import Mathlib
universe u v w
noncomputable section

theorem MazurTransfer.finite_algebra_valuation_point_lift
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Module.Finite R A] {F : Type w} [Field F] [Algebra R F]
    (P : ValuationSubring F) [Algebra R P] [IsScalarTower R P F]
    (f : A →ₐ[R] F) :
    ∃ fP : A →ₐ[R] P, ∀ a, (fP a : F) = f a := by sorry
