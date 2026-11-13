-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_V_card_Q_of_disjoint
-- name    : OddOrder.Peterfalvi.S15.coprime_card_V_card_Q_of_disjoint
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:51.986273+00:00
-- url     : https://prove2.me/theorems/8afb1f21-049e-4cec-a190-7981e1098ee1
-- title:
--   Peterfalvi (13.2.a), $T$-side: $|V|$ is coprime to $|Q|$ when $Q\cap V=1$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let `tdata : TypeIIData hyp.T` be a type II datum for $T$ and assume $Q\cap V=1$. Then
--
--   $$\gcd(|V|,|Q|)=1 .$$
--
--   This is the $T$-side dual of the coprimality of $|U|$ and $|P|$ and is used in the $V$-side of (13.17) and (14.10).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTBasic.lean#L22-L62

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem coprime_card_V_card_Q_of_disjoint [Finite G]
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.T) (hdisj : hyp.Q ⊓ hyp.V = ⊥) :
    Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.Q) := by sorry

end OddOrder.Peterfalvi.S15
