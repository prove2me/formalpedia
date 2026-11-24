-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_combine_K5
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_combine_K5
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-24T21:55:38.653492+00:00
-- url     : https://prove2.me/theorems/b96f0db6-2e83-45ec-9cd1-9b9bbc6d5786
-- title:
--   Final $K_5$ dual-jet assembly and bivariate cancellation at $U = \infty$
-- statement:
--   Combines the Branch-1 dual-jet terms at $U = \infty$ and applies `localInf_biv_identity` to identify the resulting $t^1$-coefficient with $-\operatorname{toK5\_RInf} / L_K^2$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L2847-L3085

import Definitions.Def_HodgeComputerFormal_LaurentJets
import Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
import Definitions.Def_HodgeComputerSSR_RInfData
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_combine_K5
    {w0 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2 / (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)
    (hS3Q_ne : SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K ≠ 0)
    (hT59_ne : 5 * SymmetricSexticResidual.K5Field.T_K - 9 ≠ 0)
    (hL_ne : SymmetricSexticResidual.LocalResidueU0.L_K ≠ 0) :
    let S3Q := SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K
    let T59 := 5 * SymmetricSexticResidual.K5Field.T_K - 9
    let q1_1 : SymmetricSexticResidual.K5Field.K5 := SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163
    let q1_0 : SymmetricSexticResidual.K5Field.K5 := SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u0_biv / (3 * SymmetricSexticResidual.K5Field.T_K * T59 * 107163)
    let c3_A : SymmetricSexticResidual.K5Field.K5 := (73 / 7971615 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2
    let c2_A : SymmetricSexticResidual.K5Field.K5 := SymmetricSexticResidual.LocalResidueInfAlg.A32_2_q_fn SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (14849347275 * (3 * SymmetricSexticResidual.K5Field.T_K * T59))
    let c1_A : SymmetricSexticResidual.K5Field.K5 := SymmetricSexticResidual.LocalResidueInfAlg.A32_1_q_fn SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (4949782425 * (3 * SymmetricSexticResidual.K5Field.T_K * T59) ^ 2)
    ({ val := -(279006525 / 64 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K * T59 ^ 2 / (S3Q ^ 8 * SymmetricSexticResidual.LocalResidueU0.L_K),
        eps := (13286025 / 12544 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K * T59 ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.P44_fn SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K / (S3Q ^ 11 * SymmetricSexticResidual.LocalResidueU0.L_K ^ 2) } *
      { val := w0⁻¹ ^ 3 * (73 / 7971615 * T59 * S3Q ^ 2) * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163),
        eps :=
          w0⁻¹ ^ 3 * (73 / 7971615 * T59 * S3Q ^ 2) * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_0_u1_biv / (28 * 107163 * S3Q ^ 3)) +
          w0⁻¹ ^ 3 * (SymmetricSexticResidual.LocalResidueInfAlg.M01_q_fn SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163) +
          w0⁻¹ ^ 2 * (2 / 885735 * T59 * S3Q ^ 2) * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQX_0_biv / 567) *
            (PolynomialEncoding.SignedExpressions.ringEval SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.VerticalIdentity.H0_int_e / 7) ^ 2 } +
      { val := 0,
        eps :=
          (531441 / 448 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K * T59 * (35 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.T_K + 133 * SymmetricSexticResidual.K5Field.S_K - 420 * SymmetricSexticResidual.K5Field.Q_K + 225 * SymmetricSexticResidual.K5Field.T_K - 45) / S3Q ^ 8 *
            (w0⁻¹ ^ 2 * (c3_A * q1_0 + c2_A * q1_1)) +
          -(177147 / 400 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K / S3Q ^ 5 * (w0⁻¹ * (c2_A * q1_0 + c1_A * q1_1)) } : QuadraticCovers.Dual SymmetricSexticResidual.K5Field.K5).eps =
      -SymmetricSexticResidual.LocalResidueU0.toK5_RInf / SymmetricSexticResidual.LocalResidueU0.L_K ^ 2 := by sorry
