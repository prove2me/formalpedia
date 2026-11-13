-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_betaGrid_support_of_c_eq_one
-- name    : OddOrder.Peterfalvi.S15.betaGrid_support_of_c_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:16:44.348227+00:00
-- url     : https://prove2.me/theorems/e20d738f-f998-4f43-b22b-dfe633f4bbac
-- title:
--   Peterfalvi (13.18.a): $\beta_j$ is supported on $P^\#\cup V_S^S$ when $c=1$
-- statement:
--   Let $G$ be a finite minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis (G := G)` be the Peterfalvi Section 13 hypothesis package (subgroups $P,U,W_1,W_2,S,\dots$ and parameters $p,q,u,c,\dots$). Assume $c=1$ and let $0\ne j<p$. Then the class function $\beta_j=$ `betaGrid hyp j` on $S$ has support inside
--   $$\{z\in S:\ z\in P^\#\ \cup\ V_S^{S}\},$$
--   where $P^\#$ is `sharpSubgroup hyp.P` and $V_S^{S}$ is the $S$-conjugacy class set `conjClassSetIn S (typePV S Sdata)`.
--
--   This is the exact support statement of Peterfalvi (13.18.a): $\mathrm{supp}(\beta_j)\subseteq P^\#\cup V_S^S$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean#L585-L680

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacterBasic

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in

theorem betaGrid_support_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆
      {z : ↥hyp.S |
        (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.P ∪
          OddOrder.GroupTheory.conjClassSetIn hyp.S
            (OddOrder.GroupTheory.typePV hyp.S hyp.Sdata)} := by sorry

end OddOrder.Peterfalvi.S15
