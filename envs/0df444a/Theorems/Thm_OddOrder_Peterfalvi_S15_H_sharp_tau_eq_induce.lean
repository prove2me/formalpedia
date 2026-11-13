-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_H_sharp_tau_eq_induce
-- name    : OddOrder.Peterfalvi.S15.H_sharp_tau_eq_induce
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:43:23.590192+00:00
-- url     : https://prove2.me/theorems/cfb06ee0-497f-4fbc-91da-3ec45a1d6359
-- title:
--   Peterfalvi (13.2.e)/(7.2): the $(S,H^\#)$ Dade isometry equals $\mathrm{Ind}_S^G$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let $G$ be finite (`Fintype G`, $|G|$ invertible in $\mathbb C$). Let $\alpha$ be a class function on $S$ supported on $H^\#=H\setminus\{1\}$ (an element of `SupportedClassFunctions ℂ (sharp H) S`), and let $\tau$ be the Dade isometry of the (7.1) hypothesis `H_sharp_hypothesis71 hG hyp`. Then
--
--   $$\tau(\alpha)=\mathrm{Ind}_S^G\,\alpha .$$
--
--   This is the clause of (13.2.e) that $\tau$ coincides with induction; it links the (7.7.a) coefficients with the $\tau_1$-extension.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean#L1122-L1177

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Machinery135

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in

theorem H_sharp_tau_eq_induce [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S) :
    (H_sharp_hypothesis71 hG hyp).τ α
      = ClassFunction.induce hyp.S (α : ClassFunction ↥hyp.S ℂ) := by sorry

end OddOrder.Peterfalvi.S15
