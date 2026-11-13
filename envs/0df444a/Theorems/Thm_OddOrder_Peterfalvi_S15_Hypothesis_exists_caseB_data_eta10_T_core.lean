-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_exists_caseB_data_eta10_T_core
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.exists_caseB_data_eta10_T_core
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:58:49.358111+00:00
-- url     : https://prove2.me/theorems/226a09c1-ac2e-4d4e-bbc2-42d0f51ddd96
-- title:
--   Peterfalvi (13.5)/(13.8): the $T$-side correction package for $\eta_{10}$
-- statement:
--   Let $G$ be a finite minimal simple group of odd order, `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package with subgroups $Q\le T$, and `pins : NuGridSupplyData hyp`. Assume $D=1$ and that $Q$ is commutative. Then there exist functions $\zeta,\alpha:T\to\mathbb C$ and integers $\alpha_1,\delta$ such that:
--
--   1. $\zeta(x)=0$ for $x\in T\setminus Q$;
--   2. $\sum_{x\in Q}\zeta(x)\,\overline{\alpha(x)}=0$;
--   3. $\eta_{10}(x)=\delta\,\zeta(x)+\alpha(x)$ for $x\in Q\setminus\{1\}$;
--   4. $\sum_{x\in T}|\zeta(x)|^2-|\zeta(1)|^2=|T'|-v^2$;
--   5. $\mathrm{Re}\big(\zeta(1)\overline{\alpha(1)}\big)=v\,\alpha_1$;
--   6. $\delta^2=1$;
--   7. $(q^p-1)\,\alpha_1^2\ \le\ \sum_{x\in Q\setminus\{1\}}|\alpha(x)|^2$.
--
--   Here $\eta_{10}=$ `hyp.eta10`, $T'$ is the derived subgroup of $T$ (`derivedInG hyp.T`), $v=$ `hyp.v`.
--
--   This package gives the normalized distinguished row $\zeta$, the $Q$-kernel tail $\alpha$, the point formula on $Q^\#$, the exact first term, and the inflation bound used in Peterfalvi (13.8).
--
--   **Formalization Note.** Sums over $Q$ are over `Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)`; norms are real and $q^p-1$ is a natural-number expression cast to $\mathbb R$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10Correction.lean#L200-L353

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in

theorem Hypothesis.exists_caseB_data_eta10_T_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hQcomm : IsMulCommutative ↥hyp.Q)
    (pins : NuGridSupplyData hyp) :
    ∃ (ζ α : ↥hyp.T → ℂ) (α1 δ : ℤ),
      (∀ x : ↥hyp.T, x ∉ hyp.Q.subgroupOf hyp.T → ζ x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        ζ x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1,
        hyp.eta10 ↑x = (δ : ℂ) * ζ x + α x) ∧
      ((∑ x : ↥hyp.T, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2
        = (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) ∧
      ((ζ 1 * (starRingEnd ℂ) (α 1)).re = (hyp.v : ℝ) * (α1 : ℝ)) ∧
      δ ^ 2 = 1 ∧
      ((hyp.q ^ hyp.p - 1 : ℕ) : ℝ) * ((α1 : ℤ) : ℝ) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1, ‖α x‖ ^ 2 := by sorry

end

end OddOrder.Peterfalvi.S15
