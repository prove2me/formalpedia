-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_W1_within_T_of_D_eq_bot
-- name    : OddOrder.Peterfalvi.S15.normalizer_W1_within_T_of_D_eq_bot
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:47.852112+00:00
-- url     : https://prove2.me/theorems/cbb783be-761c-4a7b-8481-9d4dc3d5bf34
-- title:
--   Peterfalvi (13.16), $T$-side with $D=1$: $N_G(W_1)\cap T\le QW_2$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $T$ is of type II and $D=1$. Then
--
--   $$N_G(W_1)\cap T\ \le\ Q\sqcup W_2 .$$
--
--   This is the $T$-internal part of the (13.16) confinement of $N_G(W_1)$, obtained via the Dedekind modular law from $V\cap N_G(W_1)=1$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTBasic.lean#L758-L852

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem normalizer_W1_within_T_of_D_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥) :
    Subgroup.normalizer (hyp.W1 : Set G) ⊓ hyp.T ≤ hyp.Q ⊔ hyp.W2 := by sorry

end OddOrder.Peterfalvi.S15
