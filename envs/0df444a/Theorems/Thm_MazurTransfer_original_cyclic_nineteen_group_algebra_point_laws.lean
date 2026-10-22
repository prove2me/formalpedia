-- Prove2me | Theorems.Thm_MazurTransfer_original_cyclic_nineteen_group_algebra_point_laws
-- name    : MazurTransfer.original_cyclic_nineteen_group_algebra_point_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T21:52:45.993343+00:00
-- url     : https://prove2.me/theorems/5f695cb2-5b66-4319-9b5c-deca6e940a13
-- statement:
--   The original cyclic nineteen group algebra has the original mutually inverse point and literal-root maps over every commutative coefficient algebra. The same generator, root characters, convolution multiplication, identity, and every coefficient map satisfy the thirteen complete original propositions. Every original type and algebra hypothesis is retained and independently checked. Named downstream consumer: normalization of the same selected integral pi quotient and pushforward of its norm Kummer classes.

import Definitions.Def_MazurTransfer_OriginalCyclicNineteenGroupAlgebraPointsData20261020
noncomputable section
open MazurTransfer.CyclicNineteenGroupAlgebraPoints

theorem MazurTransfer.original_cyclic_nineteen_group_algebra_point_laws : (Eq (instHPow.hPow MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator 19) 1) ∧ (∀ (m : MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic),
  Eq
    (instHPow.hPow MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator
      (EquivLike.toFunLike.coe Multiplicative.toAdd m).val)
    m) ∧ (∀ {T : Type} [inst : Monoid T] {f g : MonoidHom MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic T},
  Eq (MonoidHom.instFunLike.coe f MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator)
      (MonoidHom.instFunLike.coe g MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator) →
    Eq f g) ∧ (∀ {T : Type} [inst : CommRing T] (ζ : Subtype fun x => SetLike.instMembership.mem (rootsOfUnity 19 T) x),
  Eq (instHSMul.hSMul 19 (EquivLike.toFunLike.coe Additive.ofMul ζ.val)) 0) ∧ (∀ {T : Type} [inst : CommRing T] (ζ : Subtype fun x => SetLike.instMembership.mem (rootsOfUnity 19 T) x),
  Eq
    (MonoidHom.instFunLike.coe (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootCharacter ζ)
      MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator)
    ζ.val) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (f : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f).val.val
    (AlgHom.funLike.coe f.ofConv (MonoidAlgebra.single MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator 1))) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (ζ : Subtype fun x => SetLike.instMembership.mem (rootsOfUnity 19 T) x),
  Eq
    (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R
      (MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointOfRoot R ζ))
    ζ) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (f : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq
    (MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointOfRoot R
      (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f))
    f) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (f g : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R (instHMul.hMul f g))
    (instHMul.hMul (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f)
      (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R g))) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T],
  Eq (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R (1 : WithConv (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic →ₐ[R] T))) 1) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T] {T' : Type}
  [inst_3 : CommRing T'] [inst_4 : Algebra R T'] (a : AlgHom R T T')
  (f : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R { ofConv := a.comp f.ofConv })
    (MonoidHom.instFunLike.coe (restrictRootsOfUnity a.toRingHom 19)
      (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f))) ∧ (∀ (m : MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic), Eq (instHPow.hPow m 19) 1) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (f : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq
    (MonoidHom.instFunLike.coe (MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointRootsCharacter R f)
      MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator)
    (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f)) := by sorry
