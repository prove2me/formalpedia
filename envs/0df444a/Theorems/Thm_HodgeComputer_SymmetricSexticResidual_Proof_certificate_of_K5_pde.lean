-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_certificate_of_K5_pde
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.certificate_of_K5_pde
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:38:45.042554+00:00
-- url     : https://prove2.me/theorems/38a99b63-ea14-43ea-ac34-b47600515a16
-- title:
--   Lifting a $K_5$ residue-PDE solution to a complex sextic Hodge certificate
-- statement:
--   If there exists a 4-component vector $w : \operatorname{Fin} 4 \to K_5$ solving the reduced first-order divergence equation
--
--   $$\operatorname{srcX} + \operatorname{resDivW}(w) = 0$$
--
--   in the $S_3 \times S_3$-invariant hypersurface field $K_5$, then `HodgeComputer.SymmetricSexticResidual` admits a complex rational Hodge certificate with $(n, d, q) = (5, 6, 1)$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/SymmetricPiola.lean

import Definitions.Def_DiamondCertificate
import Definitions.Def_HodgeComputerSymmetricSexticResidual
import Definitions.Def_HodgeComputerSSR_K5Field
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.certificate_of_K5_pde
    (w : Fin 4 → SymmetricSexticResidual.K5Field.K5)
    (heq : SymmetricSexticResidual.K5Field.srcX + SymmetricSexticResidual.K5Field.resDivW w = 0) :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.SymmetricSexticResidual.n)
      HodgeComputer.SymmetricSexticResidual.F
      HodgeComputer.SymmetricSexticResidual.A
      HodgeComputer.SymmetricSexticResidual.d
      HodgeComputer.SymmetricSexticResidual.q := by sorry
