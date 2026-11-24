-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_sum_R34_eq_sheet_div
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.sum_R34_eq_sheet_div
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T09:38:42.283007+00:00
-- url     : https://prove2.me/theorems/733f05c1-d89c-4aa1-9fa9-a047a98069c6
-- title:
--   Sum of the 34 horizontal residues of $\eta_L$ equals a sheet divergence on $\mathrm{CoverL}$
-- statement:
--   There exists a 4-component vector $w_{H, L} : \operatorname{Fin} 4 \to \mathrm{CoverL}$ satisfying $2 W_2 H_0^2\,\operatorname{resDivW}_L(w_{H, L}) = \sum_{r \in R_{34}} \operatorname{residue}(r, \eta_L)$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverResidue.lean#L3641-L4273

import Definitions.Def_HodgeComputerFormal_RationalResidues
import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
set_option autoImplicit false
open scoped BigOperators

theorem HodgeComputer.SymmetricSexticResidual.Proof.sum_R34_eq_sheet_div :
    ∃ w_H_L : Fin 4 → SymmetricSexticResidual.CoverResidue.CoverL,
      2 * SymmetricSexticResidual.SheetCalculus.ιL (L := SymmetricSexticResidual.CoverResidue.CoverL)
          SymmetricSexticResidual.K5Field.W2_K *
        SymmetricSexticResidual.SheetCalculus.ιL (L := SymmetricSexticResidual.CoverResidue.CoverL)
          SymmetricSexticResidual.K5Field.H0_K ^ 2 *
        SymmetricSexticResidual.SheetCalculus.resDivW_L w_H_L =
        ∑ r ∈ SymmetricSexticResidual.CoverResidue.R34,
          CrossedRationalResidue.residue r SymmetricSexticResidual.CoverResidue.eta_L := by sorry
