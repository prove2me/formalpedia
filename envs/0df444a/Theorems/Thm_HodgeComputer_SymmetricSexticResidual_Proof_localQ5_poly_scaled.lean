-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_poly_scaled
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-24T22:23:01.942208+00:00
-- url     : https://prove2.me/theorems/881cc1fd-e67e-4024-b40d-e64e6a806727
-- title:
--   Nonvanishing of $(S, Q)$ denominator factors and exact scaling between $Q_5, Q_7$ and `Q5_c`, `Q7_c`
-- statement:
--   Proves `fac_4_ne`, `D_all_K5_ne`, `fac_4 = -L_K`, and the exact integer scaling identities relating `k5Params.Q5_z`, `k5Params.Q7_z`, `Q5_pol_K5`, and `Q7_pol_K5`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Alg.lean#L78-L287

import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_Q5K5Master
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled :
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.fac_4 ≠ 0) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.D_all_expr ≠ 0) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.fac_4 =
      -SymmetricSexticResidual.LocalResidueU0.L_K) ∧
    (Polynomial.C (2893401 : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.CoverAlgebra.k5Params.Q5_z =
      SymmetricSexticResidual.LocalResidueQ5.Q5_pol_K5) ∧
    (Polynomial.C (1640558367 : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.CoverAlgebra.k5Params.Q7_z =
      Polynomial.C (2 : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.LocalResidueQ5.Q7_pol_K5) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 (SymmetricSexticResidual.Q5WeightsData.Q5_c 5) =
      (SymmetricSexticResidual.Q5WeightsData.lc5_const : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.lc5_fac_expr) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.D_all_expr =
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.lc5_fac_expr *
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.D_all_div_lc5_expr) := by sorry
