-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Q_elementaryAbelian_T
-- name    : OddOrder.Peterfalvi.S15.Q_elementaryAbelian_T
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:48.333479+00:00
-- url     : https://prove2.me/theorems/9f24fd57-9cf0-4024-b10f-fa8be132eb2a
-- title:
--   Peterfalvi (14.2.a), $T$-side: $Q=T_F$ is elementary abelian of exponent $q$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $T$ is of type II. Then $Q=T_F$ is an elementary abelian $q$-group (`IsElementaryAbelian hyp.q ↥hyp.Q`).
--
--   This is the $T$-side dual of the corresponding statement for $P=S_F$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTBasic.lean#L686-L756

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem Q_elementaryAbelian_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    IsElementaryAbelian hyp.q ↥hyp.Q := by sorry

end OddOrder.Peterfalvi.S15
