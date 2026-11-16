-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_Supplement_lemma_4_8
-- name    : LatticeAvgPrec.OneVector.Supplement.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:40:11.165906+00:00
-- url     : https://prove2.me/theorems/f0c77e5f-a4ea-4cf3-8606-6bd538ec371f
-- title:
--   Lemma 4.8 — Singular values of QR blocks
-- statement:
--   Let $Y\in\mathbb R^{k\times k}$ be nonsingular and let $Y=OR$ be a QR factorization: $O^{\mathsf T}O=I$ and $R$ upper triangular. Let $1\le d\le k$ and let $R_0\in\mathbb R^{d\times d}$ be the leading diagonal block of $R$ (rows and columns $1,\dots,d$) or its trailing diagonal block (rows and columns $k-d+1,\dots,k$). Then
--
--   $$
--   \sigma_{\min}(R_0)\;\ge\;\frac{\min_j\|(R_0)_j\|_2}{\sqrt d\,\kappa_{\rm col}(Y)},
--   $$
--
--   where $(R_0)_j$ is the $j$-th column of $R_0$, $\sigma_{\min}$ is the smallest singular value and $\kappa_{\rm col}$ is the column-scaled condition number of Definition 4.3.
--
--   The bound controls the conditioning of a block of a reduced basis by the conditioning of the whole basis; in the paper it bounds the projected lengths of the quotient lattice (Proposition 4.7) and the lift of Lemma 4.11.
--
--   **Formalization Note** The two blocks are given by the index maps $i\mapsto i$ and $i\mapsto k-d+i$ on $\{0,\dots,d-1\}$; the statement covers both. $\kappa_{\rm col}(Y)$ is the published `kappaCol`, of the whole matrix $Y$.
--
--   Differences from the source:
--   - encoding: its upper-triangular QR factor → every factorization Y = OR with OᵀO = I and R upper triangular; reason: such factors differ only by row signs of R, which change neither the column norms nor σ_min of a diagonal block
--   - encoding: a leading or trailing d×d diagonal block → the blocks on indices 0..d−1 and k−d..k−1, with 1 ≤ d ≤ k, both covered; reason: Lean indexes from 0; d ≥ 1 is needed for a block to exist
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Lemma 4.8, p.18 (proof App. B.1, p.28)

import Definitions.Def_LatticeAvgPrec_OneVector_Supplement_Objects
open Matrix

namespace LatticeAvgPrec.OneVector.Supplement

/-- **Lemma 4.8** (Singular values of QR blocks; STOC 2027 submission #1574, p.18). Let
`Y ∈ ℝ^{k×k}` be nonsingular and `R_0 ∈ ℝ^{d×d}` a leading or trailing diagonal block of its
upper-triangular QR factor. Then `σ_min(R_0) ≥ min_j ‖(R_0)_j‖₂ / (√d κ_col(Y))`.

**Formalization Note** `Y = OR` with `OᵀO = I` and `R` upper triangular (every QR factor, not only
the positive one). The leading block sits on indices `0, …, d−1`, the trailing block on
`k−d, …, k−1` (the index map `e`); `1 ≤ d ≤ k`. Both blocks are covered. -/
theorem lemma_4_8 (k d : ℕ) (Y O R : Matrix (Fin k) (Fin k) ℝ) (hY : Y.det ≠ 0)
    (hYOR : Y = O * R) (hO : Oᵀ * O = 1) (hR : ∀ i j, j < i → R i j = 0)
    (hd₁ : 1 ≤ d) (hdk : d ≤ k) :
    ∀ e : Fin d → Fin k,
      (e = (fun i => ⟨i.val, by omega⟩) ∨ e = (fun i => ⟨k - d + i.val, by omega⟩)) →
      Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hd₁⟩⟩)
          (fun j => l2 (fun t => R (e t) (e j))) / (Real.sqrt d * kappaCol Y) ≤
        sigmaMin (R.submatrix e e) := by sorry

end LatticeAvgPrec.OneVector.Supplement
