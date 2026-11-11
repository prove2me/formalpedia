-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_D_2
-- name    : LpBallVI.Affine.lemma_D_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:10:23.960729+00:00
-- url     : https://prove2.me/theorems/4bd05402-9702-42c9-b4e0-a8e5509b4623
-- title:
--   Lemma D.2 — a positive rational c_R with 1 − τ ≤ c_R/R^{p−1} ≤ 1 + τ is computable in polynomial time
-- statement:
--   For every fixed rational $p > 1$ and fixed rational $\tau \in (0,1)$ there is a polynomial-time algorithm that, given a positive integer $R$ in binary, outputs a positive rational $c_R$ with
--   $$1 - \tau \le \frac{c_R}{R^{p-1}} \le 1 + \tau.$$
--   It makes the anchor coefficient of the reduction rational and polynomial-time computable.
--
--   Differences from the source:
--   - encoding: a polynomial-time algorithm given R ∈ Z+ outputs c_R → a CookPvsNP.PolyTimeComputable map f with f(encBin R) = encRat c_R for every R ≥ 1; reason: the platform notion of polynomial-time computability on binary codes
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 52, Lemma D.2, (81)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace LpBallVI.Affine

/-- **Lemma D.2**, p. 52: for every fixed rational `p > 1` and rational `τ ∈ (0, 1)` there is a
polynomial-time algorithm that, given a positive integer `R` (in binary), computes a positive
rational `c_R` with `1 − τ ≤ c_R / R^{p−1} ≤ 1 + τ`. -/
theorem lemma_D_2 (p τ : ℚ) (hp : 1 < p) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ R : ℕ, 1 ≤ R → ∃ cR : ℚ, 0 < cR ∧
        f (QAlgorithms.LocalHamiltonian.encBin R) = QAlgorithms.LocalHamiltonian.encRat cR ∧
        1 - (τ : ℝ) ≤ (cR : ℝ) / (R : ℝ) ^ ((p : ℝ) - 1) ∧
        (cR : ℝ) / (R : ℝ) ^ ((p : ℝ) - 1) ≤ 1 + (τ : ℝ) := by sorry

end LpBallVI.Affine
