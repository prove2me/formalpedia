-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_BTot_dot_W
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localQ5_BTot_dot_W
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T22:30:47.089209+00:00
-- url     : https://prove2.me/theorems/a3b87efc-889a-45e3-a881-b1ef171aa9a5
-- title:
--   Identification of `evalBTot` with the weighted dot product $\sum_{k=0}^{12} R_{12,\mathrm{int},k} W_{\mathrm{num},k}$
-- statement:
--   Proves `cacheK.ac = acK`, `cacheK.gsq = gsqK`, `D_all = cacheK.D_div_L2 * L_K^2`, the `RQ5_T` evaluation bridge, $\deg(R_{12,\mathrm{int}}) \le 12$, and `evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) = ∑ k, R12_int_p.coeff k * W_num_expr k`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Trace.lean#L1079-L1288

import Definitions.Def_HodgeComputerSSR_Q5K5Master
set_option autoImplicit false
open scoped BigOperators

theorem HodgeComputer.SymmetricSexticResidual.Proof.localQ5_BTot_dot_W :
    (SymmetricSexticResidual.LocalResidueQ5.cacheK.ac = SymmetricSexticResidual.LocalResidueQ5.acK) ∧
    (SymmetricSexticResidual.LocalResidueQ5.cacheK.gsq = SymmetricSexticResidual.LocalResidueQ5.gsqK) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.D_all_expr =
      SymmetricSexticResidual.LocalResidueQ5.cacheK.D_div_L2 *
      SymmetricSexticResidual.LocalResidueU0.L_K ^ 2) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalBivLK5
        (SymmetricSexticResidual.LocalResidueQ5.cacheK.RQ5_T.map fun row =>
          row.map fun p => PolynomialEncoding.PolyOps.uEval
            SymmetricSexticResidual.LocalResidueQ5.k5Ops p SymmetricSexticResidual.K5Field.T_K) =
      SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueData.RQ5_biv) ∧
    (SymmetricSexticResidual.LocalResidueQ5.R12_int_p.natDegree ≤ 12) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalBivLK5
        (SymmetricSexticResidual.LocalResidueQ5.evalBTot
          SymmetricSexticResidual.LocalResidueQ5.k5Ops
          SymmetricSexticResidual.LocalResidueQ5.cacheK
          SymmetricSexticResidual.LocalResidueQ5.gtK
          SymmetricSexticResidual.K5Field.T_K) =
      ∑ k : Fin 13,
        SymmetricSexticResidual.LocalResidueQ5.R12_int_p.coeff k.val *
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
          (SymmetricSexticResidual.LocalResidueQ5.W_num_expr k)) := by sorry
