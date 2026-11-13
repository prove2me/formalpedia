-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_V_inf_W1_le_centralizer_W1
-- name    : OddOrder.Peterfalvi.S15.normalizer_V_inf_W1_le_centralizer_W1
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:07:45.144537+00:00
-- url     : https://prove2.me/theorems/00bfd96b-841b-4f27-bf44-40e19de31ac0
-- title:
--   Peterfalvi (13.16): $N_V(W_1)\le C_G(W_1)$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $T$ is of type II. Then
--
--   $$V\cap N_G(W_1)\ \le\ C_G(W_1).$$
--
--   This is the crux of (13.16) on the $W_1$-side, proved by coprime fixed-point lifting for the action of $W_2$ on $V$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTBasic.lean#L319-L422

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem normalizer_V_inf_W1_le_centralizer_W1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) :
    hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) ≤ Subgroup.centralizer (hyp.W1 : Set G) := by sorry

end OddOrder.Peterfalvi.S15
