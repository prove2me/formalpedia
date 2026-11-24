-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_coprimalities_Q5
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T08:59:42.71734+00:00
-- url     : https://prove2.me/theorems/c65dd832-933f-416f-82e4-cae9f489702f
-- title:
--   All 8 nondegeneracy coprimalities for $Q_5$ over $K_5[U]$
-- statement:
--   Proves `CoverCoprimalityQ5Spec`: over $K_5[U]$, the quintic $Q_5$ is pairwise coprime to $Q_5', Q_7, U, U - 1, c_{b,h}, c_{a,h}, \mathrm{nm}_{WU}$, and $\operatorname{disc}(E_0)$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverAlgebra.lean#L3158-L3210

import Definitions.Def_HodgeComputerSSR_CoverFactors
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5 :
    SymmetricSexticResidual.CoverAlgebra.CoverCoprimalityQ5Spec := by sorry
