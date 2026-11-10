-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_rank_one_conversion
-- name    : IntegerMatrixMortality.FixedImage.rank_one_conversion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:18.337035+00:00
-- url     : https://prove2.me/theorems/77655650-aaf3-442e-b256-f2c3ac7e7aad
-- title:
--   Lemma 3.1 — Rank-one conversion
-- statement:
--   Let G be any finite set of nonsingular rational two-by-two matrices, and let s,t be rational lines, possibly equal or infinite in the affine chart. Choose nonzero integer column u spanning s and nonzero integer row λ with kernel t. Set R=uλ. Then R is a nonzero integer rank-one matrix with rational image s and rational kernel t, and
--
--   $$\operatorname{Mortal}(G\cup\{R\})\iff\exists W\in G^*,\quad W(s)=t.$$
--
--   The zero product may contain R any number of times and in arbitrary positions; W=I is allowed. No preservation of the error set is required of R.
--
--   Differences from the source:
--   - encoding: arbitrary rational lines and the rational family with integer R adjoined → rational submodules, integer outer product, and scalar inclusion of R; reason: this retains arbitrary lines including infinity, all rank/image/kernel assertions and unrestricted mixed words
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma 3.1, PDF p. 6 / printed p. 4

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem rank_one_conversion
    (G : Finset QMat) (hG : ∀ A ∈ G, A.det ≠ 0)
    (s t : Submodule ℚ QVec) (hs : IsRationalLine s) (ht : IsRationalLine t)
    (u lam : Fin 2 → ℤ) (hu : u ≠ 0) (hlam : lam ≠ 0)
    (hus : Submodule.span ℚ {integerColumn u} = s) (hlamt : rowKernel lam = t) :
      let R := OuterProduct u lam
      R ≠ 0 ∧ Module.finrank ℚ (LinearMap.range (matrixLinear (rationalMatrix R))) = 1 ∧
      LinearMap.range (matrixLinear (rationalMatrix R)) = s ∧
      LinearMap.ker (matrixLinear (rationalMatrix R)) = t ∧
      (Mortal ((G : Set QMat) ∪ {rationalMatrix R}) ↔
        ∃ w : List QMat, (∀ A ∈ w, A ∈ G) ∧
          Submodule.map (matrixLinear (wordMatrix w)) s = t) := by sorry

end IntegerMatrixMortality.FixedImage
