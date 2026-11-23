-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_limitingScheme_rounding_inequality
-- name    : GrothendieckLB.Supplement.limitingScheme_rounding_inequality
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T17:37:15.435307+00:00
-- url     : https://prove2.me/theorems/8b89f5fb-b49a-4290-a78d-f8c6d662783b
-- title:
--   Finite Gaussian projection for allowable limiting correlations
-- statement:
--   For any finite matrix and any limiting Krivine scheme, rounding at any set of unit vectors with interior cross inner products bounds the normalized correlation objective by π/2 times the sign optimum. Each allowable coordinate transformation of the cross Gram matrix is realizable by unit vectors, so different independent Gaussian projections may be assigned to each coordinate. This direct finite rounding removes the approximation by ordinary Krivine schemes from the derivation of the cubic–quintic upper bound.
-- source:
--   Saha et al., arXiv:2608.11158, Section 3 and Appendix A, https://arxiv.org/html/2608.11158v2

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_GrothendieckLB_Supplement_LimitingScheme_corr

namespace GrothendieckLB.Supplement

theorem limitingScheme_rounding_inequality {m n d k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (S : LimitingScheme k)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hstrict : ∀ i j, |inner ℝ (u i) (v j)| < 1) :
    (∑ i, ∑ j, A i j * S.corr (inner ℝ (u i) (v j))) ≤
      (Real.pi / 2) * GrothendieckConstant.optValue A := by sorry

end GrothendieckLB.Supplement
