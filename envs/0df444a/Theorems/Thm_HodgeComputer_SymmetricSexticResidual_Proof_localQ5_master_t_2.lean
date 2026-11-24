-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_2
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_2
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T22:10:28.619546+00:00
-- url     : https://prove2.me/theorems/a08f6344-2205-4021-8f7e-af3330c2f3ea
-- title:
--   Centered $T$-grid Kronecker check slice 2 ($T \in \{-5, -4\}$)
-- statement:
--   Verifies `checkMasterTChunk (-5) 2 = true`, certifying that all $(x, y)$-components of `evalTStep intOps` vanish at $(S, Q) = (2^{474}, 2^{70 \cdot 474})$ for $T \in \{-5, -4\}$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5CheckA.lean

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_2 :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (-5) 2 = true := by sorry
