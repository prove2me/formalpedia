-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_lemma_45
-- name    : GraphSimOT.Gaps.lemma_45
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:07:47.82854+00:00
-- url     : https://prove2.me/theorems/a84cf4a4-db13-4cde-a464-ecbd0ce59084
-- title:
--   Lemma 45 — spectral approximation: |ζ_Q − max_{S,T} n⁻²|Σ Q_ij Q_kℓ ⟨z_ij, T_t z_kℓ⟩|| ≤ 2t with ‖z_ij‖ ≤ √2, ‖T_t‖ ≤ 1/t
-- statement:
--   Let $G, H$ be graphs on $[n]$, $n\ge2$ (App. E.2). For every $t>0$ there are $m$ with $1\le m\le 2n$, vectors $(z_{ij})_{i,j\in[n]}$ in $\mathcal H = \mathbb R^m$ (standard inner product) with $\|z_{ij}\|\le\sqrt2$, and a linear operator $T_t$ on $\mathcal H$ with $\|T_t\|_{2\to2}\le 1/t$, such that every $Q\in\mathrm{DS}(n)$ satisfies
--   $$\Big|\zeta_Q - \max_{S,T\subseteq[n]^2}\frac1{n^2}\Big|\sum_{(i,j)\in S}\sum_{(k,\ell)\in T}Q_{ij}Q_{k\ell}\langle z_{ij}, T_tz_{k\ell}\rangle\Big|\Big|\ \le\ 2t.\qquad(30)$$
--   The vectors and the operator do not depend on $Q$.
--
--   This is the spectral heart of the additive rounding (Theorem 39): up to $2t$, the discrepancy kernel is replaced by a bounded-rank bilinear form.
--
--   Differences from the source:
--   - encoding: indices in [n] = {1, …, n} → Fin n = {0, …, n − 1}; reason: relabelling of the index set; no instance changes
--   - encoding: H = R^m with the standard inner product; a linear operator T_t with ‖T_t‖_{2→2} ≤ 1/t → EuclideanSpace ℝ (Fin m); T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) with ‖T‖ ≤ 1 / t; reason: on a finite-dimensional space every linear map is continuous, and the operator norm for the Euclidean norm is the 2→2 norm
--   - encoding: max_{S,T ⊆ [n]²} of the bilinear sum → zetaSpec z T Q, the published cut norm of the n² × n² matrix Q_ij Q_kℓ ⟨z_ij, T z_kℓ⟩ divided by n²; reason: the cut norm is that maximum
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 39, Lemma 45

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_CutRounding

namespace GraphSimOT.Gaps

/-- Lemma 45 (App. E.2.2, p. 39): for every `t > 0` there are `m` with `1 ≤ m ≤ 2n`, vectors
`z_ij ∈ ℝ^m` with `‖z_ij‖ ≤ √2` and a linear operator `T_t` on `ℝ^m` with `‖T_t‖_{2→2} ≤ 1/t`
such that every `Q ∈ DS(n)` satisfies
`|ζ_Q − max_{S,T ⊆ [n]²} n^{-2} |∑_{(i,j) ∈ S} ∑_{(k,ℓ) ∈ T} Q_ij Q_kℓ ⟨z_ij, T_t z_kℓ⟩|| ≤ 2t`. -/
theorem lemma_45 {n : ℕ} (hn : 2 ≤ n) (G H : SimpleGraph (Fin n)) (t : ℝ) (ht : 0 < t) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 2 * n ∧
      ∃ (z : Fin n → Fin n → EuclideanSpace ℝ (Fin m))
        (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)),
        (∀ i j, ‖z i j‖ ≤ Real.sqrt 2) ∧ ‖T‖ ≤ 1 / t ∧
        ∀ Q ∈ doublyStochastic ℝ (Fin n), |zeta G H Q - zetaSpec z T Q| ≤ 2 * t := by sorry

end GraphSimOT.Gaps
