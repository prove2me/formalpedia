-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_flow_shape
-- name    : MultiwayGap2325.Main.Supplement.affine_flow_shape
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:37:33.234947+00:00
-- url     : https://prove2.me/theorems/961f4877-dab2-407b-a56c-6b4f72e21e4f
-- title:
--   Affine label flows and constant weights of the explicit family
-- statement:
--   For every $q$ and every real $T$, the explicit affine construction has affine label flows and constant weights. On a face $S$ of cardinality $r$, the star-label flow is zero, while the flow for terminal label $i\in S$ is
--   $$
--   F_i^S(x)=a_r(e_i-p^S(x)),
--   \qquad p_s^S(x)=\frac{T-x_s}{rT-1}.
--   $$
--   Thus its linear part is coordinatewise $a_r x_s/(rT-1)$ on $s\in S$ (and zero elsewhere), with the remaining expression constant. Every edge weight $w_{st}^S$ is the constant $a_r/(r-1)$ and every terminal density $g_i^S$ is the constant $a_r$.
--
--   These are the structural qualifiers in Theorem 3.5, and they apply to the complete family used in Theorem 6.1 independently of validity.
--
--   **Formalization Note** The linear part is represented as a continuous linear map on the finite-dimensional coordinate space, exactly as required by `HasAffineLabelFlows`.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Theorem 3.5, p.8, and the explicit formulas (24) in Theorem 6.1, p.23.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- The shape assertions in Theorem 3.5 for every member of the affine family (24). -/
theorem affine_flow_shape (q : ℕ) (T : ℝ) :
    HasAffineLabelFlows T (affineData q T) ∧
      HasConstantWeights T (affineData q T) := by sorry
