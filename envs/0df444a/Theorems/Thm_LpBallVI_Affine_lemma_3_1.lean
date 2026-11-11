-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_3_1
-- name    : LpBallVI.Affine.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:02.655149+00:00
-- url     : https://prove2.me/theorems/0986500c-1ea4-4a23-b66c-2f02b6d480d1
-- title:
--   Lemma 3.1 — S_R(z) = R J_q(z)/‖z‖_q^{q−1} is the unique maximizer of ⟨y, z⟩ over B_p(R)
-- statement:
--   Let $1 < p < \infty$, $q = p/(p-1)$, $R > 0$ and $z \ne 0$. The support point $S_R(z) = R\,J_q(z)/\|z\|_q^{q-1}$, with $J_q(z)_i = |z_i|^{q-2}z_i$, lies in $B_p(R)$ and is the unique maximizer of $\langle y, z\rangle$ over $B_p(R)$:
--   $$S_R(z) = \operatorname*{arg\,max}_{y \in B_p(R)} \langle y, z\rangle.$$
--   It turns the VI conditions on an $\ell_p$ ball into the duality-map equation used by the reduction.
--
--   Differences from the source:
--   - encoding: ℝ^d → functions on a finite index type ι; reason: relabelling of coordinates; same instances
--   - encoding: S_R(z) is the unique maximizer → S_R(z) ∈ B_p(R), ⟨y,z⟩ ≤ ⟨S_R(z),z⟩ for all y ∈ B_p(R), and every y ∈ B_p(R) with ⟨S_R(z),z⟩ ≤ ⟨y,z⟩ equals S_R(z); reason: the three clauses of a unique maximizer
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 15, Lemma 3.1, (5)

import Mathlib
import Definitions.Def_LpBallVI_Affine_Geometry

namespace LpBallVI.Affine

/-- **Lemma 3.1**, p. 15: for `1 < p < ∞`, `R > 0` and `z ≠ 0`, the support point
`S_R(z) = R J_q(z) / ‖z‖_q^{q−1}` is the unique maximizer of `⟨y, z⟩` over `B_p(R)`. -/
theorem lemma_3_1 {ι : Type*} [Fintype ι] (p R : ℝ) (hp : 1 < p) (hR : 0 < R) (z : ι → ℝ)
    (hz : z ≠ 0) :
    supportPt p R z ∈ ball p R ∧
      (∀ y ∈ ball p R, dot y z ≤ dot (supportPt p R z) z) ∧
      ∀ y ∈ ball p R, dot (supportPt p R z) z ≤ dot y z → y = supportPt p R z := by sorry

end LpBallVI.Affine
