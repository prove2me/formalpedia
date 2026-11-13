-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_exists_conj_typeP_V_of_coprime
-- name    : OddOrder.Peterfalvi.S15.exists_conj_typeP_V_of_coprime
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:07.167341+00:00
-- url     : https://prove2.me/theorems/e33c9c4a-d709-41cd-8c75-a69e719e93f2
-- title:
--   Schur-Zassenhaus for $T$-side (13.17): $V$ is $T$-conjugate to the type-data complement
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let `tdata : TypeIIData hyp.T` be a type II datum for $T$ with type P data `tdata.typeP`, and assume $\gcd(|V|,|Q|)=1$. Then there exists $x\in T$ with
--
--   $$V=x\,(\text{`tdata.typeP.U`})\,x^{-1}.$$
--
--   Both $V$ and `tdata.typeP.U` complement $Q$ in $T'$, so this is Schur-Zassenhaus conjugacy.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTBasic.lean#L948-L1024

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_conj_typeP_V_of_coprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (tdata : TypeIIData hyp.T)
    (hcop : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.Q)) :
    ∃ x : G, x ∈ hyp.T ∧ hyp.V = MulAut.conj x • tdata.typeP.U := by sorry

end OddOrder.Peterfalvi.S15
