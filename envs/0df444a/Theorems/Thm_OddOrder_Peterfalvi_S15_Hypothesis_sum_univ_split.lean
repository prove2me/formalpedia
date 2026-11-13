-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_sum_univ_split
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.sum_univ_split
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:53:12.654197+00:00
-- url     : https://prove2.me/theorems/ff7d5740-b908-4625-a3b1-5b4697705df8
-- title:
--   The four-piece split of a conjugation-invariant sum over $G$ (counting skeleton of (13.10))
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let $G$ be a finite group (`Fintype G`) with `IsMinimalSimpleOdd G`, assume $|Q|=q^p$ and $vd\ne1$, let $M$ be an additive commutative monoid and $f:G\to M$ a class function (`f (g x g⁻¹) = f x` for all $g,x$). Put $H^\#=(PC)\setminus\{1\}$, $Q^\#=Q\setminus\{1\}$ and let $G_0=$ `hyp.G0Finset` be the set of elements of $G$ outside $\{1\}\cup(H^\#)^G\cup(Q^\#)^G$. Then
--
--   $$\sum_{x\in G}f(x)=f(1)+\sum_{x\in G_0}f(x)+[G:S]\cdot\sum_{x\in H^\#}f(x)+[G:T]\cdot\sum_{x\in Q^\#}f(x),$$
--
--   where $n\cdot m$ denotes the $n$-fold multiple in $M$.
--
--   Instances with $f=|\chi|^2$ give the Parseval splits (13.10.1), (13.10.2) and $f=1$ the cover count (13.10.3).
--
--   **Formalization Note**. $G_0$ is defined in the formalization as the complement of the other pieces (see `G0Finset`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean#L224-L310

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

open scoped Classical in

theorem Hypothesis.sum_univ_split [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    ∑ x : G, f x
      = f 1 + (∑ x ∈ hyp.G0Finset, f x)
        + hyp.S.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, f x
        + hyp.T.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, f x := by sorry

end CountingLayer

end OddOrder.Peterfalvi.S15
