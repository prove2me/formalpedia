-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_card_LF_coprime_pq
-- name    : OddOrder.Peterfalvi.S15.card_LF_coprime_pq
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:02.141545+00:00
-- url     : https://prove2.me/theorems/6780e863-70ab-4f54-873f-50444319b48e
-- title:
--   Peterfalvi (8.17.a): the Fitting kernel of a type I maximal subgroup has order prime to $pq$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let $L$ be a maximal subgroup of $G$ of type I that is conjugate neither to $S$ nor to $T$. Then
--
--   $$\gcd\big(|L_F|,\,pq\big)=1,\qquad L_F=\text{`maxNilpotentNormalHall L`}.$$
--
--   This is the coprimality (B2) derived from Theorem E of Bender-Glauberman via (8.17.a); it is used in the Section 13 analysis.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_Gate3.lean#L149-L236

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_LF_coprime_pq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (hLnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S)
    (hLnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T) :
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q) := by sorry

end OddOrder.Peterfalvi.S15
