-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_H_sharp_hypothesis76_base_cCoeff_int
-- name    : OddOrder.Peterfalvi.S15.H_sharp_hypothesis76_base_cCoeff_int
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:02:33.370216+00:00
-- url     : https://prove2.me/theorems/aec30e35-40b8-45a9-8a52-90e5f5dd61ac
-- title:
--   Peterfalvi (13.5.a): (7.7.a) coefficients of virtual characters over the chosen base are integers
-- statement:
--   Let $G$ be a finite group (`Fintype G`, with $|G|$ invertible in $\mathbb C$) with `IsMinimalSimpleOdd G`, let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration with subgroups $S,H,P,\dots$, and let $\varphi_0$ be an irreducible character of $H$ (as a subgroup of $S$). Here `H_sharp_hypothesis76_base hG hyp φ₀` is the (7.6) family of characters $\zeta_0,\dots,\zeta_n$ of $H$ (viewed inside $S$) based at $\varphi_0$, and `cCoeff χ i` is its (7.7.a) coefficient of the class function $\chi$ at index $i$. Then for every virtual character $\chi\in\mathbb Z\mathrm{Irr}(G)$ (`χ ∈ ZIrr G`) and every index $i\in\{0,\dots,n\}$ there is an integer $z$ with
--
--   $$\mathrm{cCoeff}(\chi,i)=z .$$
--
--   This is the integrality part of (13.5.a) in Section 13; the choice of base does not matter since $H=PC$ is abelian.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean#L28-L99

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped Classical in
open scoped FiniteInduce in

theorem H_sharp_hypothesis76_base_cCoeff_int [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) :
    ∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      ∃ z : ℤ, (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff χ i = (z : ℂ) := by sorry

end

end OddOrder.Peterfalvi.S15
