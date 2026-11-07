-- Prove2me | Theorems.Thm_IterRoundDet_lemma_2_9
-- name    : IterRoundDet.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:36.038046+00:00
-- url     : https://prove2.me/theorems/9675b1f8-cbd9-45cf-9546-b2281a7b0af2
-- title:
--   Lemma 2.9 — graph Laplacian subspace bound $v^\top L^\dagger v\le 2v^\top D_L^{-1}v$
-- statement:
--   Let $L\in\mathbb R^{m\times m}$ be a graph Laplacian, that is, $L$ is symmetric, $L_{ij}\le 0$ for $i\ne j$, and $L\mathbf 1=0$. Suppose $D_L=\operatorname{diag}(L_{ii})$ is positive definite. Then there is a subspace $U\subseteq\operatorname{range}L$ of dimension at least $\lceil m/2\rceil$ such that every $v\in U$ satisfies $\sum_i v_i=0$ and
--
--   $$v^\top L^\dagger v\le 2\,v^\top D_L^{-1}v.$$
--
--   It supplies the direction of positive curvature for the branch $f-g_2$.
--
--   Differences from the source:
--   - encoding: dimension at least ⌈m/2⌉ → (m + 1) / 2 ≤ finrank U, natural-number division; reason: ⌈m/2⌉ = ⌊(m+1)/2⌋
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 2.9, p.11

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Covariance

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 2.9 (Graph Laplacian subspace bound), p.11. Let `L ∈ ℝ^{m×m}` be a graph Laplacian with
`D_L = diag(L_ii)` positive definite. Then there is a subspace `U ⊆ range L` of dimension at least `⌈m/2⌉` such that
every `v ∈ U` satisfies `∑_i v_i = 0` and `v⊤L†v ≤ 2 v⊤D_L^{−1}v`. -/
theorem lemma_2_9 {m : ℕ} {L : Matrix (Fin m) (Fin m) ℝ} (hL : IsGraphLaplacian L)
    (hD : ∀ i, 0 < L i i) :
    ∃ U : Submodule ℝ (Fin m → ℝ), U ≤ LinearMap.range (Matrix.mulVecLin L) ∧
      (m + 1) / 2 ≤ Module.finrank ℝ U ∧
      ∀ v ∈ U, ∑ i, v i = 0 ∧ pinvForm L v ≤ 2 * ∑ i, v i ^ 2 / L i i := by sorry

end IterRoundDet
