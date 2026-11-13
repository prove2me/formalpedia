-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_P_conj_forall_not_le_T
-- name    : OddOrder.Peterfalvi.S15.P_conj_forall_not_le_T
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:55:12.132063+00:00
-- url     : https://prove2.me/theorems/b9941880-1da6-49cf-aba8-e9db8ae1fe3d
-- title:
--   No conjugate of $P=S_F$ lies in $T$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Then for every $w\in G$ it is not the case that $w^{-1}rw\in T$ for all $r\in P$; in other words no conjugate of $P$ is contained in $T$:
--
--   $$\forall w\in G,\ \neg\,(w^{-1}Pw\subseteq T).$$
--
--   This is the structural gate for (13.4): $|P|=p^q$ exceeds the $p$-part of $|T|$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean#L740-L832

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

theorem P_conj_forall_not_le_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ w : G, ¬ ∀ r ∈ hyp.P, w⁻¹ * r * w ∈ hyp.T := by sorry

end CountingLayer

end OddOrder.Peterfalvi.S15
