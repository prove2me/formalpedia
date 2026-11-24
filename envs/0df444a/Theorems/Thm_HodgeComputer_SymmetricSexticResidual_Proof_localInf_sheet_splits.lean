-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_sheet_splits
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T16:58:38.926983+00:00
-- url     : https://prove2.me/theorems/e0bf8a39-e035-46d0-bbb4-377a26072435
-- title:
--   $(U, V)$-degree splittings of sheet minors, $A_{0V}$, $A_X$, brackets, and $Q_Y$ cancellation
-- statement:
--   Proves the exact $(U, V)$-degree decompositions of `numM`, `A_0V`, `A_X`, the vanishing `AY_t3_U3_eq_zero`, the explicit $(1,0)/(0,0)/(1,1)$ bracket/2-form evaluations `br_*_eq`/`om_*_eq`, and the leading $Q_Y$ cancellation `QY_10_u1_zero`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInfAlg.lean#L452-L1099

import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits :
    (∀ {R : Type} [Field R] [CharZero R] (s1 q1 v1 s2 q2 v2 U V : R),
      SymmetricSexticResidual.SheetCalculus.dH_dS s1 q1 U V * SymmetricSexticResidual.SheetCalculus.dH_dQ s2 q2 v2 U V -
      SymmetricSexticResidual.SheetCalculus.dH_dS s2 q2 U V * SymmetricSexticResidual.SheetCalculus.dH_dQ s1 q1 v1 U V =
        V ^ 2 * (U ^ 3 * SymmetricSexticResidual.LocalResidueInfAlg.minor_U3 s1 q1 v1 s2 q2 v2 +
                 U ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.minor_U2 s1 q1 v1 s2 q2 v2 +
                 U * SymmetricSexticResidual.LocalResidueInfAlg.minor_U1 s1 q1 v1 s2 q2 v2 +
                 SymmetricSexticResidual.LocalResidueInfAlg.minor_U0 s1 q1 s2 q2)) ∧
    (∀ {R : Type} [Field R] [CharZero R] (mi : Fin 10) (a b xS xQ U V : R),
      SymmetricSexticResidual.SheetCalculus.numM mi a b xS xQ U V =
        V ^ 2 * (U ^ 3 * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 mi a b xS xQ +
                 U ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 2 mi a b xS xQ +
                 U * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 1 mi a b xS xQ +
                 SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 0 mi a b xS xQ)) ∧
    (∀ {R : Type} [Field R] [CharZero R] (a b xS xQ : R),
      -(123236 / 24249375 : R) * (SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 0 a b xS xQ +
        (2790 / 77) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 6 a b xS xQ +
        28 * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 8 a b xS xQ -
        (5904 / 77) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 9 a b xS xQ) +
      (492944 / 33949125) * (SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 1 a b xS xQ +
        (927 / 77) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 6 a b xS xQ +
        (49 / 5) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 8 a b xS xQ -
        (21159 / 770) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 9 a b xS xQ) = 0) ∧
    (∀ {R : Type} [Field R] [CharZero R] (a b xS xQ U V : R),
      SymmetricSexticResidual.SheetCalculus.A_0V a b xS xQ U V =
        V ^ 2 * (U ^ 3 * SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 3 a b xS xQ +
                 U ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 2 a b xS xQ +
                 U * SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 1 a b xS xQ +
                 SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 0 a b xS xQ)) ∧
    (∀ {R : Type} [Field R] [CharZero R] (a b xS xQ U V : R),
      SymmetricSexticResidual.SheetCalculus.A_X a b xS xQ U V =
        U * V ^ 2 * (U ^ 3 * SymmetricSexticResidual.LocalResidueInfAlg.AX_Uk 3 a b xS xQ +
                     U ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.AX_Uk 2 a b xS xQ +
                     U * SymmetricSexticResidual.LocalResidueInfAlg.AX_Uk 1 a b xS xQ +
                     SymmetricSexticResidual.LocalResidueInfAlg.AX_Uk 0 a b xS xQ)) ∧
    (∀ {R : Type} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R),
      243 * (SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 1 0 -
        SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 0 0) =
        match k with
        | 0 => -5 * T * (5 * T - 9) * (9 * x - 25 * S + 15 * Q)
        | 1 => -150 * T * (5 * T - 9) * S
        | 2 => 5 * (5 * T - 3) * (27 * x - 25 * S + 45 * Q) * S
        | 3 => -90 * T * (5 * T - 9) * S
        | 4 => 0) ∧
    (∀ {R : Type} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R),
      243 * SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 0 0 =
        match k with
        | 0 => 25 * T * (5 * T - 9) * (-5 * S + 3 * Q)
        | 1 => 150 * T * (5 * T - 9) * S
        | 2 => -25 * (5 * T - 3) * (-5 * S + 9 * Q) * S
        | 3 => 0
        | 4 => 0) ∧
    (∀ {R : Type} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R),
      243 * (SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 1 1 -
        SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 1 0 -
        SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 0 1 +
        SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 0 0) =
        match k with
        | 0 => -(27 * y - 25 * T + 45) * T * (9 * x - 25 * S + 15 * Q)
        | 1 => -30 * (27 * y - 25 * T + 45) * T * S
        | 2 => (9 * y - 25 * T + 15) * (27 * x - 25 * S + 45 * Q) * S
        | 3 => -18 * (27 * y - 25 * T + 45) * T * S
        | 4 => 18 * T * (27 * x - 25 * S + 45 * Q) * S) ∧
    (∀ {R : Type} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R),
      81 * (SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 1 0 -
        SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 0 0) =
        let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
          | 0, 2 => 5 * (5 * T - 3) * (9 * x - 25 * S + 15 * Q)
          | 1, 2 => 150 * (5 * T - 3) * S
          | 2, 3 => -90 * (5 * T - 3) * S
          | _, _ => 0
        f i j - f j i) ∧
    (∀ {R : Type} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R),
      81 * SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 0 0 =
        let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
          | 0, 2 => -25 * (5 * T - 3) * (-5 * S + 3 * Q)
          | 1, 2 => -150 * (5 * T - 3) * S
          | _, _ => 0
        f i j - f j i) ∧
    (∀ {R : Type} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R),
      81 * (SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 1 1 -
        SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 1 0 -
        SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 0 1 +
        SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 0 0) =
        let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
          | 0, 2 => (9 * y - 25 * T + 15) * (9 * x - 25 * S + 15 * Q)
          | 0, 4 => 18 * T * (9 * x - 25 * S + 15 * Q)
          | 1, 2 => 30 * (9 * y - 25 * T + 15) * S
          | 1, 4 => 540 * T * S
          | 2, 3 => -18 * (9 * y - 25 * T + 15) * S
          | 3, 4 => 324 * T * S
          | _, _ => 0
        f i j - f j i) ∧
    (∀ {R : Type} [Field R] [CharZero R] (S Q T x y : R),
      3 * (SymmetricSexticResidual.SheetCalculus.QY_num S Q T x y 1 0 0 -
        SymmetricSexticResidual.SheetCalculus.QY_num S Q T x y 0 0 0) +
      (SymmetricSexticResidual.SheetCalculus.QY_num S Q T x y 1 0 1 -
        SymmetricSexticResidual.SheetCalculus.QY_num S Q T x y 0 0 1) = 0) := by sorry
