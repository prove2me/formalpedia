-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_sum_RQ5_eta_L
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.sum_RQ5_eta_L
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T21:55:51.297744+00:00
-- url     : https://prove2.me/theorems/cf9f0313-643f-4923-b770-8aadaf649f25
-- title:
--   Exact sum of the five $Q_5(U) = 0$ residues of $\eta_L$
-- statement:
--   The sum of the residues of $\eta_L$ over all five roots $R_{Q_5} \subset \mathrm{CoverL}$ equals $\iota_L(\operatorname{toK5\_RQ5} / L_K^2)$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5.lean#L158-L242

import Definitions.Def_HodgeComputerFormal_RationalResidues
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_RQ5Data
set_option autoImplicit false
open scoped BigOperators

theorem HodgeComputer.SymmetricSexticResidual.Proof.sum_RQ5_eta_L :
    ∑ r ∈ SymmetricSexticResidual.CoverResidue.RQ5,
      CrossedRationalResidue.residue r SymmetricSexticResidual.CoverResidue.eta_L =
      SymmetricSexticResidual.CoverResidue.ιL_K5
        (SymmetricSexticResidual.LocalResidueU0.toK5_RQ5 /
          SymmetricSexticResidual.LocalResidueU0.L_K ^ 2) := by sorry
