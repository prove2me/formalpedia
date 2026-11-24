-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_exists_K5_pde_solution
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.exists_K5_pde_solution
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T21:59:22.806958+00:00
-- url     : https://prove2.me/theorems/761f621e-48f0-4480-950c-0c8ac66ec81b
-- title:
--   Existence of a rational solution $w \in K_5^4$ to the reduced residue PDE
-- statement:
--   There exists $w : \operatorname{Fin} 4 \to K_5$ solving $\operatorname{srcX} + \operatorname{resDivW}(w) = 0$ in the $S_3 \times S_3$-invariant hypersurface field $K_5$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/Certificate.lean#L23-L144

import Definitions.Def_HodgeComputerSSR_K5Field
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.exists_K5_pde_solution :
    ∃ w : Fin 4 → SymmetricSexticResidual.K5Field.K5,
      SymmetricSexticResidual.K5Field.srcX + SymmetricSexticResidual.K5Field.resDivW w = 0 := by sorry
