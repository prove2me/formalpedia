-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_deg_bounds
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.cover_deg_bounds
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T08:26:44.534726+00:00
-- url     : https://prove2.me/theorems/8e5d429d-e131-49d4-9da1-66bac526382f
-- title:
--   Degree bounds for $Q_5, Q_7$, and $\mathrm{nm}_z$ over $K_5[U]$
-- statement:
--   Establishes the polynomial degree bounds $\deg(Q_5) \le 5$, $\deg(Q_7) \le 7$, and $\deg(\mathrm{nm}_z) \le 73$ over $K_5[U]$ together with the branch-at-infinity valuation bounds on $W_{1,\infty}$ and $W_{2,\infty}$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverAlgebra.lean#L1748-L2340

import Definitions.Def_HodgeComputerSSR_CoverParams
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.cover_deg_bounds :
    SymmetricSexticResidual.CoverAlgebra.k5Params.Q5_z.natDegree ≤ 5 ∧
    SymmetricSexticResidual.CoverAlgebra.k5Params.Q7_z.natDegree ≤ 7 ∧
    SymmetricSexticResidual.CoverAlgebra.k5Params.nm_z.natDegree ≤ 73 := by sorry
