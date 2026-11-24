-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_biv_bridges
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T19:39:50.793233+00:00
-- url     : https://prove2.me/theorems/6086ac79-0304-429e-93f9-d0c1e8601bb7
-- title:
--   Evaluation bridges between `LocalInfBiv` ASTs and $K_5$ sheet-calculus functions
-- statement:
--   Identifies `evalBivK5` / `ringEval` of `H0_int_e`, `dH0_7_inf_e`, `QY*_biv`, `QX*_biv`, `EB*_biv`, `P44_e`, `M01_q_e`, and `A32_*_q_e` with the exact $K_5$ expressions.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L1519-L1723

import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges :
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5
        SymmetricSexticResidual.VerticalIdentity.H0_int_e =
      7 * SymmetricSexticResidual.SheetCalculus.H0_of
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (∀ k : Fin 3,
      PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5
        (SymmetricSexticResidual.LocalResidueInf.dH0_7_inf_e k) =
      7 * SymmetricSexticResidual.SheetCalculus.dH0_fn k
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QY10_biv i) =
      1701 * (SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 i -
        SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0 i)) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QX10_biv i) =
      1701 * (SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 i -
        SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0 i)) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QY00_biv i) =
      1701 * SymmetricSexticResidual.SheetCalculus.QY_num
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
        SymmetricSexticResidual.K5Field.y_K 0 0 i) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QX00_biv i) =
      1701 * SymmetricSexticResidual.SheetCalculus.QX_num
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
        SymmetricSexticResidual.K5Field.y_K 0 0 i) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QY11_biv i) =
      1701 * (SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 1 i -
        SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 i -
        SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 1 i +
        SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0 i)) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QX11_biv i) =
      1701 * (SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 1 i -
        SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 i -
        SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 1 i +
        SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0 i)) ∧
    (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.EB10_biv =
      243 * (SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 -
        SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0)) ∧
    (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.EB11_biv =
      243 * (SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 1 -
        SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 -
        SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 1 +
        SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0)) ∧
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.LocalResidueInf.P44_e =
      SymmetricSexticResidual.LocalResidueInfAlg.P44_fn
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.LocalResidueInf.M01_q_e =
      SymmetricSexticResidual.LocalResidueInfAlg.M01_q_fn
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.LocalResidueInf.A32_2_q_e =
      SymmetricSexticResidual.LocalResidueInfAlg.A32_2_q_fn
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.LocalResidueInf.A32_1_q_e =
      SymmetricSexticResidual.LocalResidueInfAlg.A32_1_q_fn
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) := by sorry
