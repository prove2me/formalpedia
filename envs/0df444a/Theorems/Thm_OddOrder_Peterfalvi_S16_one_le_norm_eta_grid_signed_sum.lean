-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_one_le_norm_eta_grid_signed_sum
-- name    : OddOrder.Peterfalvi.S16.one_le_norm_eta_grid_signed_sum
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:27:11.079202+00:00
-- url     : https://prove2.me/theorems/052be376-1261-4d7e-afa3-ad88be281a70
-- title:
--   Peterfalvi (14.11.3), arithmetic core: a signed sum over a paired $q\times p$ grid has norm at least 1
-- statement:
--   Let $q,p$ be positive odd natural numbers, and let $n,\varepsilon : \{0..q-1\}\times\{0..p-1\}\to\mathbb{Z}$ be integer grids with $\varepsilon_{ij}\in\{1,-1\}$ for all $i,j$. Suppose $n$ is invariant under the involution $(i,j)\mapsto(-i,-j)$ (`finNeg`, negation in $\mathbb{Z}/q\times\mathbb{Z}/p$): $n_{-i,-j}=n_{ij}$, and $n_{00}=1$. Then
--   $$1\;\le\;\Bigl\|\sum_{i<q}\sum_{j<p}\varepsilon_{ij}\,n_{ij}\Bigr\| ,$$
--   where the norm is the absolute value of the (integer) sum viewed as a complex number.
--
--   The involution has $(0,0)$ as its unique fixed point because $q,p$ are odd. This is the arithmetic input consumed by the generic character bound (14.11.3) and the (14.16) parity argument.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean#L1412-L1456

import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem one_le_norm_eta_grid_signed_sum {q p : ℕ} (hq : 0 < q) (hp : 0 < p)
    (hqodd : Odd q) (hpodd : Odd p) (n ε : Fin q → Fin p → ℤ)
    (hε : ∀ i j, ε i j = 1 ∨ ε i j = -1)
    (hpair : ∀ i j, n (finNeg hq i) (finNeg hp j) = n i j)
    (h00 : n ⟨0, hq⟩ ⟨0, hp⟩ = 1) :
    1 ≤ ‖(∑ i : Fin q, ∑ j : Fin p, (ε i j : ℂ) * (n i j : ℂ))‖ := by sorry

end OddOrder.Peterfalvi.S16
