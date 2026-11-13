-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_G0Finset_cyclicClosed
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.G0Finset_cyclicClosed
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:54:12.259204+00:00
-- url     : https://prove2.me/theorems/033f2019-2138-4ffa-a8dd-365e3ea9eaa0
-- title:
--   The set $G_0$ is closed under powers coprime to $|G|$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let $G_0=$ `hyp.G0Finset` be the set of elements of $G$ outside $\{1\}\cup(H^\#)^G\cup(Q^\#)^G$. Then for every $x\in G_0$ and every natural number $k$ coprime to $|G|$,
--
--   $$x^k\in G_0 .$$
--
--   This cyclic-closure property is the hypothesis shape for the Galois integrality argument that makes the atoms of (13.10) rational.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean#L990-L1027

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

theorem Hypothesis.G0Finset_cyclicClosed [Finite G] (hyp : Hypothesis (G := G)) :
    ∀ x ∈ hyp.G0Finset, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ hyp.G0Finset := by sorry

end CountingLayer

end OddOrder.Peterfalvi.S15
