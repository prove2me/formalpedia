-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_gammaGrid_real_of_c_eq_one
-- name    : OddOrder.Peterfalvi.S15.gammaGrid_real_of_c_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:19:37.687184+00:00
-- url     : https://prove2.me/theorems/8554d887-ec24-4041-8446-6546f0a36e76
-- title:
--   Peterfalvi (13.18.c): $\Gamma$ is real when $c=1$
-- statement:
--   Let $G$ be a finite minimal simple group of odd order (`IsMinimalSimpleOdd G`) with no maximal subgroup of type V, and let `hyp : Hypothesis (G := G)` be the Peterfalvi Section 13 hypothesis package (subgroups $P,U,W_1,W_2,S,\dots$ and parameters $p,q,u,c,\dots$). If $c=1$ (`hyp.c = 1`), then the class function $\Gamma=$ `GammaGrid hG hyp` is real:
--   $$\overline{\Gamma}=\Gamma .$$
--
--   This is Peterfalvi (13.18.c). Conjugation commutes with the Dade lift and with induction, and sends the grid entries to those with negated index.
--
--   **Formalization Note.** `.conj` is complex conjugation of a class function.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_BridgeCharacter.lean#L532-L588

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacterBasic
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in

theorem gammaGrid_real_of_c_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    (GammaGrid hG hyp).conj = GammaGrid hG hyp := by sorry

end OddOrder.Peterfalvi.S15
