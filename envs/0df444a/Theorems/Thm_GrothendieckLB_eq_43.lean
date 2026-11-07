-- Prove2me | Theorems.Thm_GrothendieckLB_eq_43
-- name    : GrothendieckLB.eq_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:53.296897+00:00
-- url     : https://prove2.me/theorems/9d1bb9af-b152-4b25-85bc-cae38d96feca
-- title:
--   Eqs. (43), (44): $E_1(x)\le11/6$ on $[0,1]$ and $\Delta(x)^2\ge6x^2-6x+1$ on $[r_+,1]$
-- statement:
--   Two scalar inequalities hold.
--
--   1. For $0\le x\le1$,
--   $$
--   E_1(x)=2x^2-\frac16\Delta_+(x)^2+R(x)\le\frac{11}6 .
--   $$
--   2. For $r_+\le x\le1$, with $r_+=(1+1/\sqrt3)/2$,
--   $$
--   \Delta(x)^2\ge6x^2-6x+1 .
--   $$
--
--   The first is the final step of the affine coefficient inequality, and it is tight at $x=1$. The second is the cubic correction that closes its high range.
--
--   Differences from the source:
--   - encoding: r₀ = ∞ in R(0) → Rfun through Pfun, with an explicit case at x = 0; reason: Real.log 0 = 0 in Lean; the case carries the page's convention
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eqs. (43), (44), pp.39–40

import Mathlib
import Definitions.Def_GrothendieckLB_E1
import Definitions.Def_GrothendieckLB_Delta

namespace GrothendieckLB

/-- Eqs. (43) and (44), the scalar inequality (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eqs. (43), (44), pp.39–40): `E₁(x) ≤ 11/6` for
`0 ≤ x ≤ 1`, and `Δ(x)² ≥ 6x² − 6x + 1` for `r₊ ≤ x ≤ 1`, with `r₊ = (1 + 1/√3)/2`. -/
theorem eq_43 :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, E1 x ≤ 11 / 6) ∧
    (∀ x ∈ Set.Icc ((1 + 1 / Real.sqrt 3) / 2) (1 : ℝ),
      6 * x ^ 2 - 6 * x + 1 ≤ Delta x ^ 2) := by sorry

end GrothendieckLB
