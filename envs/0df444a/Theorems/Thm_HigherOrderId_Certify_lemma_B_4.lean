-- Prove2me | Theorems.Thm_HigherOrderId_Certify_lemma_B_4
-- name    : HigherOrderId.Certify.lemma_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:17:36.86006+00:00
-- url     : https://prove2.me/theorems/54288229-7011-4525-9431-50fc6d52c45c
-- title:
--   Lemma B.4 — completion spectrum of the weighted frame: Σ a_j^{-2} ≍ m⁴ and Σ a_j^{-4} ≍ m⁶ + m⁷/w⁴
-- statement:
--   There are universal constants $c_1,C_1,c_2,C_2>0$ such that the following holds for every $d\ge10$, every $m\ge1$ with $t=m(m+1)/2\le d$ and every real $1\le w\le m$. For $U=U_w$ of (64), the map $D_U$ has full column rank, and its singular values $a_1,\dots,a_t$ satisfy
--   $$c_1m^4\le\sum_{j=1}^ta_j^{-2}\le C_1m^4,\qquad c_2\Big(m^6+\frac{m^7}{w^4}\Big)\le\sum_{j=1}^ta_j^{-4}\le C_2\Big(m^6+\frac{m^7}{w^4}\Big).$$
--
--   The second-power sum controls integrated estimation and the fourth-power sum the certification threshold; with $w\ge m^{1/4}$ the fourth-power sum is of order $m^6$, matching the universal lower bound (83).
--
--   Differences from the source:
--   - generalization: G_w lists the rows √w e_iᵀ, then (e_i + e_j)ᵀ (i < j), then d − t zero rows → the t nonzero rows are placed in any rows given by an injection ι of the frame-row index set into Fin d, all other rows zero; reason: a row permutation of U is an orthogonal change of coordinates of ℝ^d and leaves the singular values of D_U and its rank unchanged; the paper's order is one choice of ι
--   - encoding: t := m(m+1)/2 ≤ d → the existence of the injection ι : FrameRows m ↪ Fin d; reason: card (FrameRows m) = t, so ι exists exactly when t ≤ d
--   - encoding: S_w^{-1/2}; singular values w.r.t. the Frobenius norm on Sym_m → (CFC.sqrt S_w)⁻¹; square roots of the eigenvalues of the Gram matrix of D_U in an orthonormal basis of Sym_m; reason: the standard definitions; S_w is positive definite
--   - encoding: ≍ with universal comparison constants, uniformly over 1 ≤ w ≤ m → ∃ c₁ C₁ c₂ C₂ > 0 quantified before d, m, ι, w; reason: explicit form of ≍
--   - reading: "Every w is rate-optimal for integrated estimation, and w ≥ m^{1/4} also removes the unweighted frame's extra fourth-moment term." → not a separate clause; reason: commentary that follows from (66) (m⁷/w⁴ ≤ m⁶ when w ≥ m^{1/4})
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), pp. 23–24, Lemma B.4 (PDF pp. 24–25)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion

namespace HigherOrderId.Certify

/-- Lemma B.4 (completion spectrum of the weighted frame). There are universal constants such
that for every `d ≥ 10`, every `m ≥ 1` whose frame rows fit in `d` rows (`t ≤ d`, encoded by the
row placement `ι`) and every real `1 ≤ w ≤ m`, the map `D_U` for `U = U_w` has full column rank
and its singular values `a_1, …, a_t` satisfy `Σ_j a_j^{-2} ≍ m⁴` and
`Σ_j a_j^{-4} ≍ m⁶ + m⁷/w⁴`. -/
theorem lemma_B_4 :
    ∃ c₁ C₁ c₂ C₂ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < c₂ ∧ 0 < C₂ ∧
      ∀ (d m : ℕ) (ι : FrameRows m ↪ Fin d) (w : ℝ), 10 ≤ d → 1 ≤ m → 1 ≤ w → w ≤ (m : ℝ) →
        FullColRank (Uw ι w) ∧
        c₁ * (m : ℝ) ^ 4 ≤ ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 2 ∧
        ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 2 ≤ C₁ * (m : ℝ) ^ 4 ∧
        c₂ * ((m : ℝ) ^ 6 + (m : ℝ) ^ 7 / w ^ 4) ≤ ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 4 ∧
        ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 4 ≤ C₂ * ((m : ℝ) ^ 6 + (m : ℝ) ^ 7 / w ^ 4) := by sorry

end HigherOrderId.Certify
