-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_point_difference_family_fibres
-- name    : MazurTransfer.order13_actual_point_difference_family_fibres
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-08T03:06:12.477758+00:00
-- url     : https://prove2.me/theorems/a718acbe-4b9f-48c9-ad86-e639c5c24d73
-- title:
--   Actual point-difference family fibres on the order-13 curve
-- statement:
--   Let K be any field of characteristic zero and C/K the actual unchanged order-13 curve y²=x⁶+2x⁵+x⁴+2x³+6x²+4x+1 with reciprocal chart z=x⁻¹, w=yx⁻³. For any K-rational sections ε and t, write I(σ) for the ideal sheaf of the actual graph of σ. The family F=I(diagonal)ᵛ⊗I(constant ε) on C×K C and L=I(t)ᵛ⊗I(ε) on C×K Spec K are invertible sheaves. Pulling F back to the fibre at t gives an actual sheaf isomorphism to L. If K is algebraically closed, transporting L to C along C≅C×K Spec K is algebraically equivalent to zero, witnessed by the genuine geometric family. This is an intermediate geometric bridge; no Picard representing scheme, Jacobian rank, injectivity, or rational-point obstruction is assumed or claimed.
-- source:
--   Actual sextic and gluing: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Original Cartier ideal, sheaf tensor/dual/pullback, Abel–Jacobi family and algebraic-equivalence proofs: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Apache-2.0, original attribution retained. Actual curve specialization by Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory NeronModelInfra GoodReductionJacobian

theorem MazurTransfer.order13_actual_point_difference_family_fibres.{u} (K : Type u) [Field K] [CharZero K]
    (ε t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) :
    let a := MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K
    let F := (graphOver a (𝟙 _) (Category.id_comp a)).ker.invModule ⊗
      (graphOver a (a ≫ ε.1) (by rw [Category.assoc, ε.2, Category.comp_id])).ker.module
    let L := (graphOver a t.1 t.2).ker.invModule ⊗ (graphOver a ε.1 ε.2).ker.module
    Scheme.Modules.IsInvertible F ∧ Scheme.Modules.IsInvertible L ∧
      Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd a t)).obj F ≅ L) ∧
      (IsAlgClosed K → RelPicard.IsAlgEquivZero a
        ((Scheme.Modules.pullback (RelPicard.toProdSpec a)).obj L)) := by sorry
