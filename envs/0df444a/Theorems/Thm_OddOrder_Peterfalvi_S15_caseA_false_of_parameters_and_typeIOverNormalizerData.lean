-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_false_of_parameters_and_typeIOverNormalizerData
-- name    : OddOrder.Peterfalvi.S15.caseA_false_of_parameters_and_typeIOverNormalizerData
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:58.214199+00:00
-- url     : https://prove2.me/theorems/81f84d91-4411-4bc2-8282-3e1fc06090dc
-- title:
--   Peterfalvi (14.6): case (9.7.a) is impossible at the sharp parameters
-- statement:
--   Let $G$ be a finite minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis (G := G)` be the Peterfalvi Section 13 hypothesis package (subgroups $P,U,W_1,W_2,S,\dots$ and parameters $p,q,u,c,\dots$). Let `chief` be a chief-factor datum for the associated Types I--V setup of $S$ and assume the Clifford case A data `caseA : CliffordCaseAData (hyp.mkSection11CharacterDataS hG chief)`. Suppose $c=1$, $q=3$ and $u=(p-1)^2/4$, and suppose given the type-I maximal subgroup data `data : TypeIOverNormalizerData hyp` over $N_G(U)$ constructed in (13.17)/(14.5). Then
--   $$\texttt{False}.$$
--
--   That is, case (9.7.a) cannot occur at the parameters $c=1$, $q=3$, $u=(p-1)^2/4$ of (13.12)/(13.13). The proof finds a prime $r\mid (p-1)/2$ with noncyclic Sylow subgroup in $U$, then derives a contradiction from the type-I subgroup.
--
--   **Formalization Note.** $p-1$ and the division by $4$ are in $\mathbb N$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseAContradiction.lean#L46-L104

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

theorem caseA_false_of_parameters_and_typeIOverNormalizerData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData
      (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hc : hyp.c = 1) (hq : hyp.q = 3)
    (hu : hyp.u = (hyp.p - 1) ^ 2 / 4)
    (data : TypeIOverNormalizerData hyp) : False := by sorry

end OddOrder.Peterfalvi.S15
