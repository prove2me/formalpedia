-- Prove2me | Theorems.Thm_GrothendieckLB_linear_mass_bound
-- name    : GrothendieckLB.linear_mass_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:43.554828+00:00
-- url     : https://prove2.me/theorems/36483b25-be9a-4ad5-baa8-d01fe440ae89
-- title:
--   Linear-mass bound: $\|P_1F\|\le\nu$ for $|F|\le1$, and $|b_1(f,g)|\le1$
-- statement:
--   Two bounds hold in every dimension $d$.
--
--   1. For every measurable $F:\mathbb R^d\to\mathbb R$ with $|F|\le1$, one has $\|P_1F\|\le\nu$.
--   2. For every measurable sign pair $f,g$, one has
--   $$
--   \Big|\frac\pi2\langle P_1f,P_1g\rangle\Big|\le\frac\pi2\nu^2=1 .
--   $$
--
--   The first clause gives $x=\|P_1h\|/\nu\in[0,1]$ for the agreement part $h$. The second gives the upper bound on $b_1$ needed for the majorant barrier.
--
--   Differences from the source:
--   - generalization: the bound for the ternary h (p.33) and for a sign function (p.43) → every measurable F with |F| ≤ 1; reason: the page's proof uses only |F| ≤ 1 (p.33: "h ∈ [−1,1]"); both page instances are specializations
--   - generalization: odd sign functions (Part II introduction, p.30; p.43) → every measurable sign pair, oddness not assumed; reason: Definition 10.1 mixes sign pairs without oddness and the Section 7–8 argument never uses it; the odd case is a specialization
--   - encoding: P₁, P₃ as orthogonal projections in L² → moment sums p1Inner, p3Inner; reason: the moments are the coordinates of the projections in the orthonormal Hermite basis
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.2, p.33; proof of the lower bound, p.43

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_p1Norm
import Definitions.Def_ABPOnline_cG

namespace GrothendieckLB

/-- The linear-mass bound (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.2, p.33 and the proof of the lower bound, p.43): `‖P₁F‖ ≤ ν`
for every measurable `F` with `|F| ≤ 1`, and `|b₁(f, g)| ≤ (π/2)ν² = 1` for every measurable sign pair.

**Formalization Note** The first clause covers the page's two uses (`h` on p.33, a sign function on
p.43). No oddness.

`ABPOnline.cG` is the published constant `ν = √(2/π) = E|Z|` (p.31). -/
theorem linear_mass_bound (d : ℕ) :
    (∀ F : (Fin d → ℝ) → ℝ, Measurable F → (∀ x, |F x| ≤ 1) → p1Norm F ≤ ABPOnline.cG) ∧
    (∀ f g : (Fin d → ℝ) → ℝ, IsSignFn f → IsSignFn g →
      |(Real.pi / 2) * p1Inner f g| ≤ 1) := by sorry

end GrothendieckLB
