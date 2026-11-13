-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_betaL_grid_coeff_bessel
-- name    : OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.betaL_grid_coeff_bessel
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:38:05.028687+00:00
-- url     : https://prove2.me/theorems/6c4760b0-4f0d-4058-9d38-bb9b469d48b9
-- title:
--   Peterfalvi (13.19.c): Bessel bound $\sum m_{ij}^2\le pq$ for $\langle\beta_L,\eta_{ij}\rangle$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group with no maximal subgroup of type V (`hnoV`), `hncH0C : S13.H0CNoncoherenceRefuter G`, and `hyp` a Peterfalvi §14 configuration with primes $p,q$ and grid $\eta_{ij}$. Let $L$ be a maximal subgroup of $G$ and `dataL : TypeICoherent78Data L`. Let $\beta_L=$ `(dataL.h78 hG).beta` and assume the complement index satisfies $e_L = pq$. Let $m_{ij}\in\mathbb{Z}$ ($i<q$, $j<p$) satisfy $\langle\beta_L,\eta_{ij}\rangle = m_{ij}$ for all $i,j$. Then
--   $$\sum_{i<q}\sum_{j<p} m_{ij}^2 \;\le\; pq .$$
--
--   Proof idea: by the (7.8.a) decomposition $\beta_L = 1_G - \zeta_0^\nu + aW + \Gamma_L$, and orthogonality of all coherent images to the grid, $m_{ij}=\langle 1_G+\Gamma_L,\eta_{ij}\rangle$. Bessel's inequality and $\|\Gamma_L\|^2\le e_L-1$ give $\sum m_{ij}^2\le 1+(pq-1)$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLMBasic.lean#L163-L313

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

theorem betaL_grid_coeff_bessel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L)
    (hepq : (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j) = (m i j : ℂ)) :
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2
      ≤ (hyp.base.p * hyp.base.q : ℤ) := by sorry

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
