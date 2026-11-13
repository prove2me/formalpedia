-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_typeIGrid_betaL_inner_eta_eq_h78_beta
-- name    : OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.typeIGrid_betaL_inner_eta_eq_h78_beta
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:23:23.207599+00:00
-- url     : https://prove2.me/theorems/8e2a7dda-d1fe-4c9b-ac0a-a46451ec4381
-- title:
--   Peterfalvi (13.19.b): $\eta$-grid coefficients of $\beta_L$ do not depend on the choice of coherent family member
-- statement:
--   Let $G$ be a finite minimal simple odd-order group with no maximal subgroup of type V (`hnoV`), `hncH0C : S13.H0CNoncoherenceRefuter G`, and `hyp` a Peterfalvi §14 configuration. Let $M$ be a maximal subgroup of $G$ and `dataM : TypeICoherent78Data M`. Let `grid : S15.TypeIOrthogonalityGridData hyp.base dataM` be the type-I orthogonality grid data from §13, and assume the distinguished member `grid.phi` of the grid data lies in the coherent family `dataM.typeIHyp.Sset`. Then, whenever `[Fintype G]` and `[Invertible (Nat.card G : ℂ)]` are available, for all $i<q$ and $j<p$:
--   $$\langle \beta_{\mathrm{grid}},\ \eta_{ij}\rangle \;=\; \langle \beta_{M},\ \eta_{ij}\rangle ,$$
--   where $\beta_{\mathrm{grid}}$ is `grid.betaL`, $\beta_M$ is `coherentBeta hG dataM` (from the §7.8 coherent bundle), and $\eta_{ij}$ are the grid characters of `hyp.base`.
--
--   The two $\beta$'s need not be equal as class functions; only their grid coefficients agree, since the difference of two coherent images is orthogonal to the $\eta$-grid by (13.19.b). This choice-free synchronization is needed in (14.11.2).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean#L321-L449

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in

theorem typeIGrid_betaL_inner_eta_eq_h78_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M)
    (grid : OddOrder.Peterfalvi.S15.TypeIOrthogonalityGridData
      hyp.base dataM)
    (hphi : grid.phi ∈ dataM.typeIHyp.Sset) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner grid.betaL (hyp.base.eta i j) =
          ClassFunction.inner (coherentBeta hG dataM) (hyp.base.eta i j) := by sorry

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
