-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_exists_typeI_maximal_overNormalizer_V
-- name    : OddOrder.Peterfalvi.S15.exists_typeI_maximal_overNormalizer_V
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:06.497004+00:00
-- url     : https://prove2.me/theorems/9973d26f-127f-4cfe-9c5a-b6b6e9ec2172
-- title:
--   Peterfalvi (13.17.a/b), $T$-side: a maximal subgroup over $N_G(V)$ is of type I with $V\subseteq L_F$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume no maximal subgroup of $G$ is of type V, and that $T$ is of type II. Then there is a maximal subgroup $L$ of $G$ of type I such that
--
--   $$N_G(V)\le L\quad\text{and}\quad V\le L_F=\text{`maxNilpotentNormalHall L`}.$$
--
--   This is the $T$-side dual of the corresponding statement for $U$ in (13.17.a/b).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_Gate3.lean#L703-L817

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_typeI_maximal_overNormalizer_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) :
    ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ IsTypeI L ∧
      Subgroup.normalizer (hyp.V : Set G) ≤ L ∧ hyp.V ≤ maxNilpotentNormalHall L := by sorry

end OddOrder.Peterfalvi.S15
