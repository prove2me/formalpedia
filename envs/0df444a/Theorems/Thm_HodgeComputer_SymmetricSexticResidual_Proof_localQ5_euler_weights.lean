-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_euler_weights
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localQ5_euler_weights
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T22:43:18.877981+00:00
-- url     : https://prove2.me/theorems/f52067b7-f490-4b9c-9994-5be4465d91ca
-- title:
--   Exact Euler power-sum weights over the five roots $R_{Q_5}$
-- statement:
--   For every $k \in \{0, \dots, 12\}$, $\sum_{r \in R_{Q_5}} r^k / (Q_7(r) Q_5'(r)) = \iota_L(\operatorname{W\_K5\_scaled}(k))$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Alg.lean#L756-L1164

import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_Q5K5Master
set_option autoImplicit false
open scoped BigOperators

theorem HodgeComputer.SymmetricSexticResidual.Proof.localQ5_euler_weights (k : Fin 13) :
    ∑ r ∈ SymmetricSexticResidual.CoverResidue.RQ5,
      r ^ k.val /
        ((SymmetricSexticResidual.CoverAlgebra.k5Params.Q7_z.map
            SymmetricSexticResidual.CoverResidue.ιL_K5).eval r *
          (SymmetricSexticResidual.CoverAlgebra.k5Params.Q5_z.map
            SymmetricSexticResidual.CoverResidue.ιL_K5).derivative.eval r) =
      SymmetricSexticResidual.CoverResidue.ιL_K5
        (SymmetricSexticResidual.LocalResidueQ5.W_K5_scaled k) := by sorry
