-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_p4_trace
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localQ5_p4_trace
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T22:32:15.500978+00:00
-- url     : https://prove2.me/theorems/689e483c-a7cd-4322-8d00-8caee1bd3008
-- title:
--   Exact trace formula $\operatorname{Tr}(\eta_{A_C,\mathrm{main}}) = R_{12,\mathrm{int}} / (81 C_{v0} M_R Q_7 Q_5)$
-- statement:
--   Identifies the cover trace $\operatorname{Tr}_{A_C / \operatorname{RatFunc}(K_5)}(\eta_{A_C,\mathrm{main}})$ with $R_{12,\mathrm{int}}(U) / (81 C_{v0} M_R Q_7(U) Q_5(U))$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Trace.lean#L637-L1018

import Definitions.Def_HodgeComputerSSR_Q5ACDefs
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localQ5_p4_trace :
    Algebra.trace (RatFunc SymmetricSexticResidual.K5Field.K5)
        SymmetricSexticResidual.CoverResidue.A_C
        SymmetricSexticResidual.LocalResidueQ5.eta_AC_main =
      SymmetricSexticResidual.CoverResidue.toRat SymmetricSexticResidual.LocalResidueQ5.R12_int_p /
        (RatFunc.C (81 * SymmetricSexticResidual.CoverAlgebra.k5Params.Cv0 *
            (SymmetricSexticResidual.LocalResidueQ5.M_R_int : SymmetricSexticResidual.K5Field.K5)) *
          SymmetricSexticResidual.CoverResidue.toRat
            (SymmetricSexticResidual.CoverAlgebra.k5Params.Q7_z *
              SymmetricSexticResidual.CoverAlgebra.k5Params.Q5_z)) := by sorry
