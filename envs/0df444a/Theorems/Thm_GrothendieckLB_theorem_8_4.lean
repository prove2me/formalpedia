-- Prove2me | Theorems.Thm_GrothendieckLB_theorem_8_4
-- name    : GrothendieckLB.theorem_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:54.229876+00:00
-- url     : https://prove2.me/theorems/ff57a4d2-3e69-45c9-af87-385cc2a313d3
-- title:
--   Theorem 8.4: fiber residual bound #1
-- statement:
--   Let $f,g:\mathbb R^d\to\{\pm1\}$ be measurable, with agreement part $h$, disagreement part $k$ and $x=\|P_1h\|/\nu$. Then
--   $$
--   \|P_3k\|^2\le\nu^2\big(3(1-x)-(1-x)^2\big).
--   $$
--   This is the branch of $R(x)$ used on the middle and high ranges of the scalar inequality.
--
--   Differences from the source:
--   - generalization: odd sign functions (Part II introduction, p.30; p.43) → every measurable sign pair, oddness not assumed; reason: Definition 10.1 mixes sign pairs without oddness and the Section 7–8 argument never uses it; the odd case is a specialization
--   - encoding: stated after rotating coordinates so that S points along P₁h (Section 8.2, p.33) → frame-free statement in terms of ‖P₁h‖ and ‖P₃k‖²; reason: these quantities are rotation invariant, so no instance changes
--   - encoding: P₁, P₃ as orthogonal projections in L² → moment sums p1Inner, p3Inner; reason: the moments are the coordinates of the projections in the orthonormal Hermite basis
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 8.4, Eq. (40), p.37

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_agreePart
import Definitions.Def_GrothendieckLB_disagreePart
import Definitions.Def_GrothendieckLB_p1Norm
import Definitions.Def_GrothendieckLB_p3NormSq
import Definitions.Def_ABPOnline_cG

namespace GrothendieckLB

/-- Theorem 8.4, fiber residual bound #1 (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 8.4, Eq. (40), p.37): for every measurable sign
pair, with `x = ‖P₁h‖/ν`, `‖P₃k‖² ≤ ν²(3(1 − x) − (1 − x)²)`.

**Formalization Note** No oddness; free of the rotated frame of Section 8.2.

`ABPOnline.cG` is the published constant `ν = √(2/π) = E|Z|` (p.31). -/
theorem theorem_8_4 {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    p3NormSq (disagreePart f g) ≤
      ABPOnline.cG ^ 2 * (3 * (1 - p1Norm (agreePart f g) / ABPOnline.cG) -
        (1 - p1Norm (agreePart f g) / ABPOnline.cG) ^ 2) := by sorry

end GrothendieckLB
