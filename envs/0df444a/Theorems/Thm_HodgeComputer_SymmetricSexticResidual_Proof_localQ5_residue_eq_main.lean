-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_residue_eq_main
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localQ5_residue_eq_main
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-24T22:32:02.945115+00:00
-- url     : https://prove2.me/theorems/42a10e93-cf7b-4aa2-86f1-018bfe265c2f
-- title:
--   Regularity of $\eta_{A_C,\mathrm{reg}}$ on $R_{Q_5}$ and reduction to $\eta_{A_C,\mathrm{main}}$
-- statement:
--   For every root $r \in R_{Q_5}$, $\operatorname{residue}(r, \eta_L) = \operatorname{residue}(r, \operatorname{mapRatFunc}(\iota_L)(\operatorname{Tr}(\eta_{A_C,\mathrm{main}})))$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Alg.lean#L1228-L1679

import Definitions.Def_HodgeComputerFormal_CoverResidues
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_Q5ACDefs
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localQ5_residue_eq_main
    (r : SymmetricSexticResidual.CoverResidue.CoverL)
    (hr : r ∈ SymmetricSexticResidual.CoverResidue.RQ5) :
    CrossedRationalResidue.residue r SymmetricSexticResidual.CoverResidue.eta_L =
      CrossedRationalResidue.residue r
        (QuadraticCovers.mapRatFunc SymmetricSexticResidual.CoverResidue.ιL_K5
          (Algebra.trace (RatFunc SymmetricSexticResidual.K5Field.K5)
            SymmetricSexticResidual.CoverResidue.A_C
            SymmetricSexticResidual.LocalResidueQ5.eta_AC_main)) := by sorry
