-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_TypeICoherent78Data_etaGrid_projection_sub_beta_norm_one
-- name    : OddOrder.Peterfalvi.S16.TypeICoherent78Data.etaGrid_projection_sub_beta_norm_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:06:50.903198+00:00
-- url     : https://prove2.me/theorems/fd95391e-559b-4d51-ae3e-a97328fdbdf5
-- title:
--   Peterfalvi (14.11.2): the removed character $X-\beta$ has norm one
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, $L\le G$, `data : TypeICoherent78Data L`, and `hyp` a Peterfalvi §13 configuration with grid $\eta_{ij}$ ($i<q$, $j<p$). Let $\beta$ denote `(data.h78 hG).beta` and $e$ the complement index `(data.h78 hG).complementIndex`. Let $m : \{0..q-1\}\times\{0..p-1\}\to\mathbb{Z}$ with $m_{ij}\in\{1,-1\}$ for all $i,j$, assume $e = pq$ and $\langle\beta,\eta_{ij}\rangle = m_{ij}$ for all $i,j$. Put $X = \sum m_{ij}\eta_{ij}$ (`etaGridProjection hyp m`). Then
--   $$\langle X-\beta,\ X-\beta\rangle = 1 .$$
--
--   By orthonormality $\langle X,X\rangle = \langle\beta,X\rangle=\langle X,\beta\rangle = pq$, and the Dade source-norm evaluation gives $\langle\beta,\beta\rangle=pq+1$. This norm-one fact feeds the classification of $\chi = X-\beta$ as a coherent image in (14.11.2).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean#L289-L371

import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped BigOperators

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem etaGrid_projection_sub_beta_norm_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (data : TypeICoherent78Data L)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ)
    (hpm : ∀ i j, m i j = 1 ∨ m i j = -1)
    (heq : (data.h78 hG).complementIndex = hyp.p * hyp.q)
    (hcoeff : ∀ i j,
      ClassFunction.inner (data.h78 hG).beta (hyp.eta i j) = (m i j : ℂ)) :
    ClassFunction.inner
        (etaGridProjection hyp m - (data.h78 hG).beta)
        (etaGridProjection hyp m - (data.h78 hG).beta) = 1 := by sorry

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16
