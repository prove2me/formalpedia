-- Prove2me | Theorems.Thm_GrothendieckLB_eq_35_36
-- name    : GrothendieckLB.eq_35_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:52:15.661072+00:00
-- url     : https://prove2.me/theorems/e143102f-81ff-47e8-abd3-c9d313fc3b43
-- title:
--   Eqs. (36), (35): $D_1(h,k)$, $B_1(f,g)$ and $2\langle P_1f,P_1g\rangle-\langle P_3f,P_3g\rangle$ are at most $\frac{11}6\nu^2$
-- statement:
--   Let $f,g:\mathbb R^d\to\{\pm1\}$ be measurable, with agreement part $h$ and disagreement part $k$. Then
--   $$
--   D_1(h,k)\le\frac{11}6\nu^2,\qquad B_1(f,g)\le\frac{11}6\nu^2,\qquad 2\langle P_1f,P_1g\rangle-\langle P_3f,P_3g\rangle\le\frac{11}6\nu^2 .
--   $$
--   The last inequality, multiplied by $\pi/2$, is the affine coefficient inequality $b_3\ge2b_1-11/6$. Since it is affine in $(b_1,b_3)$ it passes to mixtures and coefficientwise limits. The hyperplane pair $f=g=\operatorname{sgn}(X_1)$ attains equality.
--
--   Differences from the source:
--   - generalization: odd sign functions (Part II introduction, p.30; p.43) → every measurable sign pair, oddness not assumed; reason: Definition 10.1 mixes sign pairs without oddness and the Section 7–8 argument never uses it; the odd case is a specialization
--   - encoding: P₁, P₃ as orthogonal projections in L² → moment sums p1Inner, p3Inner; reason: the moments are the coordinates of the projections in the orthonormal Hermite basis
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eqs. (35), (36), pp.32–33; Section 8.5, p.40

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_agreePart
import Definitions.Def_GrothendieckLB_disagreePart
import Definitions.Def_GrothendieckLB_B1
import Definitions.Def_GrothendieckLB_D1
import Definitions.Def_GrothendieckLB_p1Inner
import Definitions.Def_GrothendieckLB_p3Inner
import Definitions.Def_ABPOnline_cG

namespace GrothendieckLB

/-- Eqs. (36), (35) and the Hermite form of (34) for all sign pairs (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eqs. (35), (36), pp.32–33, and
Section 8.5, p.40): `D₁(h, k) ≤ (11/6)ν²`, `B₁(f, g) ≤ (11/6)ν²` and
`2⟨P₁f, P₁g⟩ − ⟨P₃f, P₃g⟩ ≤ (11/6)ν²`.

**Formalization Note** No oddness of `f, g`, which is what the mixed schemes of Definition 10.1 need.

`ABPOnline.cG` is the published constant `ν = √(2/π) = E|Z|` (p.31). -/
theorem eq_35_36 {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    D1 (agreePart f g) (disagreePart f g) ≤ 11 / 6 * ABPOnline.cG ^ 2 ∧
    B1 f g ≤ 11 / 6 * ABPOnline.cG ^ 2 ∧
    2 * p1Inner f g - p3Inner f g ≤ 11 / 6 * ABPOnline.cG ^ 2 := by sorry

end GrothendieckLB
