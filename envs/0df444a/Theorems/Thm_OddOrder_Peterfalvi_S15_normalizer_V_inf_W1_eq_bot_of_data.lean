-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_V_inf_W1_eq_bot_of_data
-- name    : OddOrder.Peterfalvi.S15.normalizer_V_inf_W1_eq_bot_of_data
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:10.015345+00:00
-- url     : https://prove2.me/theorems/ed084c3f-c676-4aec-b642-38433738a7f2
-- title:
--   Peterfalvi (13.16): $V\cap N_G(W_1)=1$ from coprimality data
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $T$ is of type II, that $\gcd(|Q|,|V\sqcup W_2|)=1$, that $Q$ is an elementary abelian $q$-group, and that $V\cap C_G(Q)=1$. Then
--
--   $$V\cap N_G(W_1)=1 .$$
--
--   This assembles the $W_1$-side core of (13.16) from the crux $N_V(W_1)\le C_G(W_1)$ using coprime action on the abelian group $Q$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTBasic.lean#L424-L587

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem normalizer_V_inf_W1_eq_bot_of_data [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T)
    (hcop : Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥(hyp.V ⊔ hyp.W2)))
    (hQ_elemAb : IsElementaryAbelian hyp.q ↥hyp.Q)
    (hDbot : hyp.V ⊓ Subgroup.centralizer (hyp.Q : Set G) = ⊥) :
    hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) = ⊥ := by sorry

end OddOrder.Peterfalvi.S15
