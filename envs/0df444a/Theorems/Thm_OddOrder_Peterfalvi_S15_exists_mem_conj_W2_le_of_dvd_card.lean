-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_exists_mem_conj_W2_le_of_dvd_card
-- name    : OddOrder.Peterfalvi.S15.exists_mem_conj_W2_le_of_dvd_card
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:07:35.582226+00:00
-- url     : https://prove2.me/theorems/3b4e325e-c96f-4fc5-97cd-8104594ef606
-- title:
--   A subgroup of $Q\rtimes W_2$ of order divisible by $p$ contains a $Q$-conjugate of $W_2$
-- statement:
--   Let $G$ be a finite group and $Q,W_2,E\le G$ subgroups. Assume $W_2\le N_G(Q)$, $Q$ is solvable, $Q\cap W_2=1$, $p$ is a prime with $|W_2|=p$ and $p\nmid|Q|$, $E\le Q\sqcup W_2$ and $p\mid|E|$. Then there is $y\in Q$ with
--
--   $$yW_2y^{-1}\ \le\ E .$$
--
--   This is the group-theoretic core of the step $\exists y\in Q,\ W_2^y\le E$ of Peterfalvi (13.17.c), proved by Cauchy and Schur-Zassenhaus conjugacy.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTDefs.lean#L55-L155

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedTransport
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroupQuotient
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_mem_conj_W2_le_of_dvd_card [Finite G]
    {Q W2 E : Subgroup G} (hWnorm : W2 ≤ Subgroup.normalizer (Q : Set G))
    (hQsolv : Group.IsSolvable ↥Q) (hdisj : Q ⊓ W2 = ⊥)
    {p : ℕ} (hp : p.Prime) (hW2 : Nat.card ↥W2 = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hE : E ≤ Q ⊔ W2) (hpE : p ∣ Nat.card ↥E) :
    ∃ y ∈ Q, (MulAut.conj y • W2 : Subgroup G) ≤ E := by sorry

end OddOrder.Peterfalvi.S15
