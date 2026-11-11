-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_4_2
-- name    : OptimalLCA.Matching.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:09.63642+00:00
-- url     : https://prove2.me/theorems/9f032950-3d55-48fc-b513-71bd47fca99f
-- title:
--   Lemma 4.2 — scalar area inequality for r₈(x,q) = qx² + 8q log q
-- statement:
--   Let $r_8(x,q)=qx^2+8q\log q$ for $|x|\le1$, $q\ge0$ (with $0\log0=0$). Then $r_8$ is convex on this domain, and for any three points $(x_i,q_i)$ of it with centroid $(\bar x,\bar q)$,
--   $$\sum_{i=1}^3r_8(x_i,q_i)-3r_8(\bar x,\bar q)\ge\tfrac13\big|(x_2-x_1)(q_3-q_1)-(q_2-q_1)(x_3-x_1)\big|.$$
--   It is the scalar building block of the area convexity of $R_\alpha$ (Lemma 4.3).
--
--   Differences from the source:
--   - encoding: 0 log 0 = 0 → Real.log 0 = 0, so 8·0·log 0 = 0; reason: same function
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 18, Lemma 4.2

import Mathlib
import Definitions.Def_OptimalLCA_Matching_SaddlePoint

namespace OptimalLCA.Matching

/-- Lemma 4.2 (scalar area inequality). `r₈(x, q) = q x² + 8 q log q` is convex on
`{|x| ≤ 1, q ≥ 0}`, and for any three points `(xᵢ, qᵢ)` there with centroid `(x̄, q̄)`,
`∑ r₈(xᵢ, qᵢ) - 3 r₈(x̄, q̄) ≥ ⅓ |(x₂ - x₁)(q₃ - q₁) - (q₂ - q₁)(x₃ - x₁)|`. -/
theorem lemma_4_2 :
    ConvexOn ℝ {p : ℝ × ℝ | |p.1| ≤ 1 ∧ 0 ≤ p.2} (fun p => r8 p.1 p.2) ∧
    ∀ x₁ q₁ x₂ q₂ x₃ q₃ : ℝ, |x₁| ≤ 1 → 0 ≤ q₁ → |x₂| ≤ 1 → 0 ≤ q₂ → |x₃| ≤ 1 → 0 ≤ q₃ →
      (1 / 3 : ℝ) * |(x₂ - x₁) * (q₃ - q₁) - (q₂ - q₁) * (x₃ - x₁)| ≤
        r8 x₁ q₁ + r8 x₂ q₂ + r8 x₃ q₃ -
          3 * r8 ((x₁ + x₂ + x₃) / 3) ((q₁ + q₂ + q₃) / 3) := by sorry

end OptimalLCA.Matching
