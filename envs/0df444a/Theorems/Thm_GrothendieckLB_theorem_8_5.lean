-- Prove2me | Theorems.Thm_GrothendieckLB_theorem_8_5
-- name    : GrothendieckLB.theorem_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:56.904933+00:00
-- url     : https://prove2.me/theorems/c4095003-8418-4c70-bfe5-1b8a07a1d965
-- title:
--   Theorem 8.5: fiber residual bound #2
-- statement:
--   Let $f,g:\mathbb R^d\to\{\pm1\}$ be measurable, with agreement part $h$, disagreement part $k$ and $x=\|P_1h\|/\nu$. Then
--   $$
--   \|P_3k\|^2\le2\Phi(\sqrt{-2\log x})-1,
--   $$
--   where at $x=0$ the right side is read through the convention $r_0=\infty$ of the proof, so it equals $1$. This cruder bound takes over from Theorem 8.4 at small $x$.
--
--   Differences from the source:
--   - generalization: odd sign functions (Part II introduction, p.30; p.43) → every measurable sign pair, oddness not assumed; reason: Definition 10.1 mixes sign pairs without oddness and the Section 7–8 argument never uses it; the odd case is a specialization
--   - encoding: stated after rotating coordinates so that S points along P₁h (Section 8.2, p.33) → frame-free statement in terms of ‖P₁h‖ and ‖P₃k‖²; reason: these quantities are rotation invariant, so no instance changes
--   - encoding: r₀ = ∞ in the proof, with the display written through log x → Pfun with an explicit case at x = 0; reason: Real.log 0 = 0 in Lean; the case carries the page's convention
--   - encoding: P₁, P₃ as orthogonal projections in L² → moment sums p1Inner, p3Inner; reason: the moments are the coordinates of the projections in the orthonormal Hermite basis
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 8.5, Eq. (41), p.38

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_agreePart
import Definitions.Def_GrothendieckLB_disagreePart
import Definitions.Def_GrothendieckLB_p1Norm
import Definitions.Def_GrothendieckLB_p3NormSq
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_Pfun

namespace GrothendieckLB

/-- Theorem 8.5, fiber residual bound #2 (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 8.5, Eq. (41), p.38): for every measurable sign
pair, with `x = ‖P₁h‖/ν`, `‖P₃k‖² ≤ 2Φ(√(−2 log x)) − 1`, with the convention `r₀ = ∞` of the
proof at `x = 0`.

**Formalization Note** `Pfun` carries the convention; no oddness; free of the rotated frame.

`ABPOnline.cG` is the published constant `ν = √(2/π) = E|Z|` (p.31). -/
theorem theorem_8_5 {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    p3NormSq (disagreePart f g) ≤ Pfun (p1Norm (agreePart f g) / ABPOnline.cG) := by sorry

end GrothendieckLB
