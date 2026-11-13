-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Q_W2_structure
-- name    : OddOrder.Peterfalvi.S15.Q_W2_structure
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:11.185176+00:00
-- url     : https://prove2.me/theorems/6f665d22-438a-4697-ac71-df47d9d07c4a
-- title:
--   Structure of $Q\rtimes W_2$: $W_2$ normalizes $Q$, $Q\cap W_2=1$ and $p\nmid|Q|$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $T$ is of type II. Then
--
--   $$W_2\le N_G(Q),\qquad Q\cap W_2=1,\qquad p\nmid |Q| .$$
--
--   This supplies the semidirect product structure $Q\rtimes W_2$ used in the $\exists y$ step of (13.17.c).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_Gate3.lean#L893-L944

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem Q_W2_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    hyp.W2 ≤ Subgroup.normalizer (hyp.Q : Set G) ∧ hyp.Q ⊓ hyp.W2 = ⊥ ∧
      ¬ hyp.p ∣ Nat.card ↥hyp.Q := by sorry

end OddOrder.Peterfalvi.S15
