-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_lSide_expansion_classification
-- name    : OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.lSide_expansion_classification
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:38:09.484142+00:00
-- url     : https://prove2.me/theorems/6a99217b-c2f1-45b4-b100-6bfe95099dd2
-- title:
--   Peterfalvi (14.11.2) on the $L$-side: $\beta_L^\tau$ is a signed $\eta$-grid sum minus a unit-norm $\chi$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group with no maximal subgroup of type V (`hnoV`), `hncH0C : S13.H0CNoncoherenceRefuter G`, and `hyp` a Peterfalvi §14 configuration with parameters $p,q,u,v$ and grid $\eta_{ij}$. Let $L$ be a maximal subgroup of $G$ and `dataL : TypeICoherent78Data L`. Write $\beta=$ `(dataL.h78 hG).beta`, $\nu=$ `(dataL.h78 hG).nu`, $\zeta_*=$ the distinguished member `(dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct`. Assume
--
--   - $q=3$ and $p=5$;
--   - the complement index $e_L = pq$;
--   - $\dfrac{u-1}{q} < \dfrac{|H|-1}{j}$ and $\dfrac{v-1}{p} < \dfrac{|H|-1}{j}$ in $\mathbb{Q}$ (with $u-1$, $v-1$, $|H|-1$ computed in $\mathbb{N}$), where $|H|$ is `Nat.card dataL.typeIHyp.H` and $j$ is the index in $L$ of the subgroup `(maxNilpotentNormalHall L).subgroupOf L`, the maximal normal nilpotent Hall subgroup of $L$ regarded inside $L$.
--
--   Then there are signs $\varepsilon_{ij}\in\{1,-1\}$ ($i<q$, $j<p$) and a class function $\chi$ on $G$ such that $\chi=\nu(\zeta_*)$ or $\chi = -\nu(\overline{\zeta_*})$, and
--   $$\beta \;=\; \sum_{i<q}\sum_{j<p}\varepsilon_{ij}\,\eta_{ij} \;-\; \chi .$$
--
--   This is the $L$-instance of the general (14.11.2) expansion: the rigidity of the $\eta$-grid projection and the norm-one classification of the removed character are combined with the Bessel bound.
--
--   **Formalization Note.** The index $j$ is `((maxNilpotentNormalHall L).subgroupOf L).index`, cast to $\mathbb{Q}$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLMBasic.lean#L433-L542

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem lSide_expansion_classification [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hepq : (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q)
    (hub_u : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) <
      ((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ))
    (hub_v : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) <
      ((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ)) :
    ∃ (signs : Fin hyp.base.q → Fin hyp.base.p → ℤ) (chi : ClassFunction G ℂ),
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
      (chi = (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct) ∨
        chi = -((dataL.h78 hG).nu
          (((dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct).conj))) ∧
      (dataL.h78 hG).beta =
        (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
            (signs i j : ℂ) • hyp.base.eta i j) - chi := by sorry

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
