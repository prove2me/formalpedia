-- Prove2me | Theorems.Thm_GrothendieckLB_corollary_8_2
-- name    : GrothendieckLB.corollary_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:36.215108+00:00
-- url     : https://prove2.me/theorems/a8d7123d-c943-4a59-bd30-6d746dfd226e
-- title:
--   Corollary 8.2: the diagonal bound
-- statement:
--   Let $h:\mathbb R^d\to\{-1,0,1\}$ be measurable and put $x=\|P_1h\|/\nu$. Then
--   $$
--   \|P_3h\|^2\ge\frac{\nu^2}6\Delta_+(x)^2,
--   $$
--   and consequently
--   $$
--   2\|P_1h\|^2-\|P_3h\|^2\le\nu^2\Big(2x^2-\frac16\Delta_+(x)^2\Big).
--   $$
--   This is the lower bound on $\|P_3h\|^2$ that controls the agreement part of $D_1$.
--
--   Differences from the source:
--   - generalization: h, k built from odd sign functions (Part II introduction, p.30) → every measurable ternary function; reason: the argument uses only the values of the function; each ternary function is the part of a sign pair, and the odd case is a specialization
--   - encoding: stated after rotating coordinates so that S points along P₁h (Section 8.2, p.33) → frame-free statement in terms of ‖P₁h‖ and ‖P₃k‖²; reason: these quantities are rotation invariant, so no instance changes
--   - encoding: P₁, P₃ as orthogonal projections in L² → moment sums p1Inner, p3Inner; reason: the moments are the coordinates of the projections in the orthonormal Hermite basis
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Corollary 8.2, p.35

import Mathlib
import Definitions.Def_GrothendieckLB_IsTernaryFn
import Definitions.Def_GrothendieckLB_p1Norm
import Definitions.Def_GrothendieckLB_p3NormSq
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_DeltaPlus

namespace GrothendieckLB

/-- Corollary 8.2, the diagonal bound (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Corollary 8.2, p.35): for every measurable ternary `h`
on `ℝ^d`, with `x = ‖P₁h‖/ν`, `‖P₃h‖² ≥ (ν²/6)Δ₊(x)²` and consequently
`2‖P₁h‖² − ‖P₃h‖² ≤ ν²(2x² − Δ₊(x)²/6)`.

**Formalization Note** The statement is free of the rotated frame of Section 8.2, because it only
involves the rotation-invariant quantities `‖P₁h‖` and `‖P₃h‖²`.

`ABPOnline.cG` is the published constant `ν = √(2/π) = E|Z|` (p.31). -/
theorem corollary_8_2 {d : ℕ} {h : (Fin d → ℝ) → ℝ} (hh : IsTernaryFn h) :
    ABPOnline.cG ^ 2 / 6 * DeltaPlus (p1Norm h / ABPOnline.cG) ^ 2 ≤ p3NormSq h ∧
    2 * p1Norm h ^ 2 - p3NormSq h ≤
      ABPOnline.cG ^ 2 * (2 * (p1Norm h / ABPOnline.cG) ^ 2 - DeltaPlus (p1Norm h / ABPOnline.cG) ^ 2 / 6) := by sorry

end GrothendieckLB
