-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_regularAt_eta_L_of_notMem
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.regularAt_eta_L_of_notMem
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T09:31:45.492166+00:00
-- url     : https://prove2.me/theorems/ef9d2aba-fa57-460e-b45f-8862d499377c
-- title:
--   Global regularity of $\eta_L$ outside $\{0\} \cup R_{Q_5} \cup R_{34}$
-- statement:
--   For every point $r \in \mathrm{CoverL}$ outside $\{0\} \cup R_{Q_5} \cup R_{34}$, the rational function $\eta_L \in \operatorname{RatFunc}(\mathrm{CoverL})$ is regular at $r$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverResidue.lean#L2151-L2700

import Definitions.Def_HodgeComputerFormal_RationalResidues
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
set_option autoImplicit false
open scoped Classical

theorem HodgeComputer.SymmetricSexticResidual.Proof.regularAt_eta_L_of_notMem
    (r : SymmetricSexticResidual.CoverResidue.CoverL)
    (hr : r ∉ ({0} ∪ SymmetricSexticResidual.CoverResidue.RQ5 ∪
      SymmetricSexticResidual.CoverResidue.R34 : Finset SymmetricSexticResidual.CoverResidue.CoverL)) :
    CrossedRationalResidue.RegularAt r SymmetricSexticResidual.CoverResidue.eta_L := by sorry
