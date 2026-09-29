-- Prove2me | Theorems.Thm_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin
-- name    : FreyPackage.ModMCarrier.rescaleLin_eq_levelInclusionLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/57d76413-79ba-5c3b-8f6c-1c60f7622b68
-- title:
--   Rescaling with d=1 equals the level inclusion
-- statement:
--   Let $R$ and $M$ be natural numbers with $M$ nonzero, and let $h$ be a proof of $1 \cdot R \mid M$ and $hRM$ a proof of $R \mid M$. Let $k$ be an integer and let $f$ be a cusp form of weight $k$ for $\Gamma_0(R)$. The assertion is the equality, inside the space of weight-$k$ cusp forms for $\Gamma_0(M)$, of the two images of $f$: on one side [`FreyPackage.ModMCarrier.rescaleLin h k f`](def/FreyPackage_ModMCarrier_Rescale.html#L140), the cusp form whose underlying function on the upper half-plane is $f \mid_k \mathrm{heckeDiagMatrix}\,1$, that is the weight-$k$ slash of $f$ by the matrix attached to the parameter $d = 1$ in the rescaling construction; on the other side [`FreyPackage.ModMCarrier.levelInclusionLin hRM k f`](def/FreyPackage_ModMCarrier_OldSublattice.html#L22), the cusp form with the same underlying function as $f$, its $\Gamma_0(M)$-invariance and vanishing at the cusps of level $M$ being obtained from those of $f$ through the inclusion $\Gamma_0(M) \le \Gamma_0(R)$ supplied by $R \mid M$.
--
--   This identifies the first of the two degeneracy maps $S_k(\Gamma_0(R)) \to S_k(\Gamma_0(M))$ in its two formal spellings: the $d = 1$ case of the rescaling operator $V_d$ and the plain level-raising inclusion. It is used where statements about oldforms formulated with rescaling operators must be matched with statements formulated with the inclusion, and is cited in the cohomological carrier argument [`CohCarrier.eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms`](thm.html#CohCarrier.eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin.lean

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem FreyPackage.ModMCarrier.rescaleLin_eq_levelInclusionLin {R M : ℕ} [NeZero M]
    (h : 1 * R ∣ M) (hRM : R ∣ M) (k : ℤ) (f : CuspForm (Gamma0 R) k) :
    FreyPackage.ModMCarrier.rescaleLin h k f = FreyPackage.ModMCarrier.levelInclusionLin hRM k f := by sorry
