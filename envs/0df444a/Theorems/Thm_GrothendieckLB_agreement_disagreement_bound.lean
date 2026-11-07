-- Prove2me | Theorems.Thm_GrothendieckLB_agreement_disagreement_bound
-- name    : GrothendieckLB.agreement_disagreement_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:52:45.528578+00:00
-- url     : https://prove2.me/theorems/a332a604-c7be-46ca-8062-28d2cebd3ce5
-- title:
--   Section 8.1: $B_1(f,g)\le 2\|P_1h\|^2-\|P_3h\|^2+\|P_3k\|^2$
-- statement:
--   Let $f,g:\mathbb R^d\to\{\pm1\}$ be measurable, with agreement part $h=(f+g)/2$ and disagreement part $k=(f-g)/2$. Then
--   $$
--   B_1(f,g)\le 2\|P_1h\|^2-\|P_3h\|^2+\|P_3k\|^2=D_1(h,k).
--   $$
--   The term $\|P_1k\|^2$ cancels on the right, which is why the strip $b_3\ge2b_1-11/6$ reduces to bounds on three quantities only.
--
--   Differences from the source:
--   - generalization: odd sign functions (Part II introduction, p.30; p.43) → every measurable sign pair, oddness not assumed; reason: Definition 10.1 mixes sign pairs without oddness and the Section 7–8 argument never uses it; the odd case is a specialization
--   - encoding: P₁, P₃ as orthogonal projections in L² → moment sums p1Inner, p3Inner; reason: the moments are the coordinates of the projections in the orthonormal Hermite basis
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.1, p.32

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_agreePart
import Definitions.Def_GrothendieckLB_disagreePart
import Definitions.Def_GrothendieckLB_B1
import Definitions.Def_GrothendieckLB_D1

namespace GrothendieckLB

/-- Section 8.1, the agreement–disagreement bound (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.1, p.32): for every measurable
sign pair with `h = (f + g)/2` and `k = (f − g)/2`,
`B₁(f, g) ≤ 2‖P₁h‖² − ‖P₃h‖² + ‖P₃k‖²`.

**Formalization Note** No oddness of `f, g`. -/
theorem agreement_disagreement_bound {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    B1 f g ≤ D1 (agreePart f g) (disagreePart f g) := by sorry

end GrothendieckLB
