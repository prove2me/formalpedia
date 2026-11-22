-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_regular
-- name    : MultiwayGap2325.Main.Supplement.affine_regular
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:53:16.46558+00:00
-- url     : https://prove2.me/theorems/bd36b533-0151-473b-8df2-b9131897dfe8
-- title:
--   Affine flow data are regular
-- statement:
--   Fix $q\ge2$ and $T\in(1/2,1)$. The affine data of equations (23)–(24), with one cell $\Omega_S$ on every truncated face, satisfy the regularity requirements for a flow instance: the cells form the required subdivisions, weights and terminal densities are measurable, nonnegative, symmetric and bounded, label flows are continuously differentiable and bounded on cells, unsupported coordinates vanish, flows are tangent, and normal components match on cell walls. The allowances are nonnegative and integrable. Since each face has only one cell, normal matching is vacuous in the proof in the paper.
--
--   **Formalization Note** This isolates `FlowData.Regular` for the explicit function `affineData q T`; it does not assume any of the other flow-instance conditions.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Theorem 6.1 and the regularity paragraph of its proof, pp.23–24; regularity requirements in §5.1.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, pp.23–24: the one-cell affine weighting and label flows satisfy all regularity conditions of §5.1. -/
theorem affine_regular (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    (affineData q T).Regular T := by sorry
