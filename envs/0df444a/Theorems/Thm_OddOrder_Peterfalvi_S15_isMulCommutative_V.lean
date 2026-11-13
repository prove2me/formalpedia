-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_isMulCommutative_V
-- name    : OddOrder.Peterfalvi.S15.isMulCommutative_V
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:04.550911+00:00
-- url     : https://prove2.me/theorems/16cf7aa0-1457-42b7-a79e-0fc6faf20fbd
-- title:
--   Peterfalvi (13.2.a), $T$-side: the complement $V$ is abelian
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $T$ is of type II. Then $V$ is commutative (`IsMulCommutative ↥hyp.V`).
--
--   This is the $T$-side analogue of the commutativity of $U$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTBasic.lean#L252-L317

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem isMulCommutative_V [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) : IsMulCommutative ↥hyp.V := by sorry

end OddOrder.Peterfalvi.S15
