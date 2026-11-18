-- Prove2me | Theorems.Thm_OWMR_arb_protected_newsvendor
-- name    : OWMR.arb_protected_newsvendor
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:34.748833+00:00
-- url     : https://prove2.me/theorems/20513240-93ab-4d87-8ced-1cb708a8cc7b
-- title:
--   Protected newsvendor under association: pooling a subset of retailers costs no more than the aggregate (C.18)
-- statement:
--   Let a network satisfy the standing assumptions and have associated demand components (`Associated`), and let $P$ be a set of retailers. Let $D^P_t=\sum_{i\in P}D_{t,i}$, i.i.d. over periods, and $\phi(y)=hy^++py^-$. Then
--   $$\inf_z\ \mathbb E\,\phi\Bigl(z-\sum_{j<L_0}D^P_j\Bigr)\le\inf_y f_{L_0}(y),\qquad f_{L_0}(y)=\mathbb E\,\phi\bigl(y-D^{(L_0)}\bigr),$$
--   where $D^{(L_0)}$ is the aggregate demand of all retailers over $L_0$ periods. The newsvendor problem of a sub-aggregate is no harder than that of the whole aggregate.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix C, Step 4, (C.16)-(C.18), pp. E.14-E.15 (association of demand components, Esary, Proschan and Walkup 1967).

import Definitions.Def_owmr_consolidation_policy

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem arb_protected_newsvendor {n : ℕ} (N : Network n) (hN : N.Standing) (hA : N.Associated)
    (P : Finset (Fin n)) :
    ⨅ z : ℝ, ∫ w, whLoss N.h N.p (z - ∑ j, (w j : ℝ))
        ∂(Measure.pi fun _ : Fin N.L0 =>
          (N.μ.map (fun x : DemandVec n => (∑ i ∈ P, x i : ℝ≥0)) : Measure ℝ≥0))
      ≤ ⨅ y : ℝ, N.fL0 y := by sorry
end OWMR
