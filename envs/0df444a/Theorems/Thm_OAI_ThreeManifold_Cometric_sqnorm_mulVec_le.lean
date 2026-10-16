-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Cometric_sqnorm_mulVec_le
-- name    : OAI.ThreeManifold.Cometric.sqnorm_mulVec_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:22:42.286598+00:00
-- url     : https://prove2.me/theorems/bddae3fa-7daf-4c54-a077-cf72262fabfa
-- title:
--   Norm bound for a $2\times2$ matrix with bounded entries
-- statement:
--   For $p\in\mathbb{R}^2$ write $|p|^2=p_0^2+p_1^2$. Let $M$ be a real $2\times2$ matrix and $B\ge0$ a real number with $|M_{ij}|\le B$ for all $i,j\in\{0,1\}$. Then for every $p\in\mathbb{R}^2$,
--   $$
--   |Mp|^2\le 4B^2\,|p|^2 .
--   $$
--
--   This is the elementary bound $\|M\|_{\mathrm{op}}^2\le\|M\|_F^2\le 4\max_{ij}|M_{ij}|^2$ for $2\times2$ matrices. It converts entrywise bounds on the error matrices of the neck cometric into bounds on their action on vectors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L1128-L1141

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Matrix
open scoped Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Cometric.sqnorm_mulVec_le {M : Mat2} {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i j, |M i j| ≤ B) (p : V2) :
    sqnorm (M *ᵥ p) ≤ 4 * B ^ 2 * sqnorm p := by sorry
