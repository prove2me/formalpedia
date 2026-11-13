-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_H_sharp_hypothesis76_base_alphaFun_inflation
-- name    : OddOrder.Peterfalvi.S15.H_sharp_hypothesis76_base_alphaFun_inflation
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:59:23.701053+00:00
-- url     : https://prove2.me/theorems/a7b4b8dc-4395-4b6b-9b05-dad6187147e3
-- title:
--   Peterfalvi (13.5.c): inflation bound for the correction function over the chosen base
-- statement:
--   Let $G$ be a finite group (`Fintype G`, $|G|$ invertible in $\mathbb C$) with `IsMinimalSimpleOdd G`, let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration, let $\varphi_0$ be an irreducible character of $H$ (as a subgroup of $S$), and let $\chi$ be any class function on $G$. Let $\alpha_\chi=$ `hypothesis76AlphaFun` be the correction function of the (7.6) family based at $\varphi_0$ (with respect to $P\le S$) attached to $\chi$; it is a function on $S$. Then
--
--   $$(p^q-1)\,|\alpha_\chi(1)|^2\ \le\ \sum_{x\in H\setminus\{1\}}|\alpha_\chi(x)|^2 ,$$
--
--   the sum running over the nonidentity elements of $H\le S$.
--
--   This is the $S$-side, chosen-base specialization of the generic inflation bound of (13.5.c).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean#L395-L439

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

theorem H_sharp_hypothesis76_base_alphaFun_inflation [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S)) (χ : ClassFunction G ℂ) :
    ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) *
        ‖hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) χ 1‖ ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
            (hyp.P.subgroupOf hyp.S) χ x‖ ^ 2 := by sorry

end

end OddOrder.Peterfalvi.S15
