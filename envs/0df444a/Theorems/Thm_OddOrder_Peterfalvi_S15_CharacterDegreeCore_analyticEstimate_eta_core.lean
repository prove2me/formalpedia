-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_analyticEstimate_eta_core
-- name    : OddOrder.Peterfalvi.S15.CharacterDegreeCore.analyticEstimate_eta_core
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:02:24.764857+00:00
-- url     : https://prove2.me/theorems/2da8dddc-5df4-419c-910f-b096c953111b
-- title:
--   Peterfalvi (13.7)--(13.8): second analytic estimate of (13.10), Core form
-- statement:
--   Let $G$ be a finite minimal simple group of odd order, `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package and `core : CharacterDegreeCore hyp` the Core character-degree data. Assume $D=1$ (`hyp.D = ⊥`), $v=(q^p-1)/(q-1)$, that $Q$ is commutative, and that `pins : NuGridSupplyData hyp` is given. Then
--   $$1\ \ge\ \frac1{|G|}+\frac{\texttt{normSqSumQ}\ G_0\ \eta_{10}}{|G|}+\frac{|H|-1}{|S|}+\Big(\frac1p-\frac1{p(q-1)}+\frac1{p(q-1)q^{p}}\Big),$$
--   where $G_0=$ `hyp.G0Finset`, $\eta_{10}=$ `hyp.eta10`, and the sum is over rational numbers.
--
--   This is the second analytic estimate in Peterfalvi (13.10), assembled from the $H^\#$ and $Q^\#$ lower bounds of (13.7)--(13.8).
--
--   **Formalization Note.** `hv` is an equation of natural numbers (with natural division); the statement is for the scoped `FiniteInduce` instances.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/AnalyticRelayer.lean#L104-L237

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped FiniteInduce in

theorem CharacterDegreeCore.analyticEstimate_eta_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    (1 : ℚ) ≥ 1 / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ)
        + ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ)
        + (1 / (hyp.p : ℚ) - 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1))
          + 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1) * (hyp.q : ℚ) ^ hyp.p)) := by sorry

end

end OddOrder.Peterfalvi.S15
