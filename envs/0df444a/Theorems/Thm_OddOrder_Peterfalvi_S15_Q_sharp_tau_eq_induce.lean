-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Q_sharp_tau_eq_induce
-- name    : OddOrder.Peterfalvi.S15.Q_sharp_tau_eq_induce
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:55:17.095727+00:00
-- url     : https://prove2.me/theorems/c48605c1-d87e-4d05-963b-9a6de77c6a48
-- title:
--   Peterfalvi (13.2.e)/(7.2) for $T$: the $(T,Q^\#)$ Dade isometry equals $\mathrm{Ind}_T^G$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let $G$ be finite (`Fintype G`, $|G|$ invertible in $\mathbb C$) and assume $vd\ne1$. Let $\alpha$ be a class function on $T$ supported on $Q^\#=Q\setminus\{1\}$ (an element of `SupportedClassFunctions ℂ (sharp Q) T`), and let $\tau$ be the Dade isometry of the (7.1) hypothesis `Q_sharp_hypothesis71 hG hyp hvd`. Then
--
--   $$\tau(\alpha)=\mathrm{Ind}_T^G\,\alpha .$$
--
--   This links the $T$-side coefficients of (7.7.a) with the $\tau_1$-coherence of the induction; it is the mirror of the corresponding $S$-side statement for $H^\#$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean#L931-L988

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

open scoped FiniteInduce in

theorem Q_sharp_tau_eq_induce [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T) :
    (Q_sharp_hypothesis71 hG hyp hvd).τ α
      = ClassFunction.induce hyp.T (α : ClassFunction ↥hyp.T ℂ) := by sorry

end CountingLayer

end OddOrder.Peterfalvi.S15
