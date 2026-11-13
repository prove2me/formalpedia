-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_analytic_inequality_of_caseB_facts
-- name    : OddOrder.Peterfalvi.S15.CharacterDegreeCore.analytic_inequality_of_caseB_facts
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:00:27.123994+00:00
-- url     : https://prove2.me/theorems/88cd953e-3c34-4ea6-bc6e-454eb9432b1b
-- title:
--   Peterfalvi (13.10): $u/c>m\,p^{q-1}/q$
-- statement:
--   Let $G$ be a finite minimal simple group of odd order, `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package with parameters $u,c,m,p,q$, `core : CharacterDegreeCore hyp` and `lam : LambdaClusterData hyp`. Assume $D=1$, $v=(q^p-1)/(q-1)$, $Q$ commutative, and `pins : NuGridSupplyData hyp`. Then
--   $$\frac{u}{c}\ >\ \frac{m\,p^{\,q-1}}{q}$$
--   (as rational numbers).
--
--   This is the endpoint of Peterfalvi (13.10): the explicit case-B facts and the Core/cluster character data force the inequality.
--
--   **Formalization Note.** The hypothesis on $v$ is an equation of natural numbers with natural division, and $p^{q-1}$ is computed in $\mathbb N$ before casting.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/AnalyticRelayer.lean#L537-L561

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

theorem CharacterDegreeCore.analytic_inequality_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ) := by sorry

end

end OddOrder.Peterfalvi.S15
