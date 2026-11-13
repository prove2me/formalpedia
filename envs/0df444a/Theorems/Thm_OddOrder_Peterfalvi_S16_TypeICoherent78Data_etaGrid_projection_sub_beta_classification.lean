-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_TypeICoherent78Data_etaGrid_projection_sub_beta_classification
-- name    : OddOrder.Peterfalvi.S16.TypeICoherent78Data.etaGrid_projection_sub_beta_classification
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:07:58.858725+00:00
-- url     : https://prove2.me/theorems/41f8c32d-e89d-471c-b9cb-e5be0214bcca
-- title:
--   Peterfalvi (14.11.2): classification of the removed unit-norm character $\chi=X-\beta$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, $L\le G$, `data : TypeICoherent78Data L`, and `hyp` a Peterfalvi §13 configuration with grid $\eta_{ij}$. Write $\beta$ for `(data.h78 hG).beta`, $\nu$ for `(data.h78 hG).nu` (the coherent map), $\zeta_t$ for `(data.h78 hG).hyp76.zeta t`, and $\zeta_*$ for the distinguished member $\zeta_{\texttt{zetaDistinct}}$. Let $m : \{0..q-1\}\times\{0..p-1\}\to\mathbb{Z}$ and $X=$ `etaGridProjection hyp m`, $\chi = X - \beta$. Assume
--
--   - for every $t \in \{0,\dots,n\}$ with $t\ne \texttt{data.ind1H}$ and all $i,j$: $\langle\nu(\zeta_t),\eta_{ij}\rangle = 0$ (every coherent family image is orthogonal to the grid);
--   - $\langle\chi,\chi\rangle = 1$.
--
--   Then
--   $$\chi = \nu(\zeta_*)\quad\text{or}\quad \chi = -\,\nu\bigl(\overline{\zeta_*}\bigr).$$
--
--   That is, $\chi$ is either the distinguished coherent image or the negative of the coherent image of its conjugate.
--
--   **Formalization Note.** The conclusion is a `let χ := …` binding followed by the disjunction.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean#L373-L545

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
set_option backward.isDefEq.respectTransparency false in

theorem etaGrid_projection_sub_beta_classification [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (data : TypeICoherent78Data L)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ)
    (heta : ∀ (t : Fin (data.n + 1)), t ≠ data.ind1H →
      ∀ i j, ClassFunction.inner
        ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta t)) (hyp.eta i j) = 0)
    (hchi1 : ClassFunction.inner
      (etaGridProjection hyp m - (data.h78 hG).beta)
      (etaGridProjection hyp m - (data.h78 hG).beta) = 1) :
    let χ := etaGridProjection hyp m - (data.h78 hG).beta
    χ = (data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) ∨
    χ = -((data.h78 hG).nu
      ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj) := by sorry

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16
