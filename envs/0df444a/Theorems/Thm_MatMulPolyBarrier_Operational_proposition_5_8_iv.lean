-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_proposition_5_8_iv
-- name    : MatMulPolyBarrier.Operational.proposition_5_8_iv
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:29.698258+00:00
-- url     : https://prove2.me/theorems/36376ca5-ac11-4cca-bd1b-2c13d58b2602
-- title:
--   Proposition 5.8(iv) — $x^{1-p}y^p\le F^\star_\theta(x,y,x+y-1)\le x^{p_2}y^p$
-- statement:
--   Let $\theta\in\Theta$ and $p:=p_1$. For all positive integers $x,y,z$ with $z=x+y-1$,
--   $$x^{1-p}y^{p}\le F^\star_\theta(x,y,z)\le x^{p_2}y^{p}.$$
--   The lower bound is used for (D2) and the upper bound for (R3) in the proof of Proposition 5.9.
--
--   Differences from the source:
--   - encoding: p = p₁ and p₂ → pExp θ 0 and pExp θ 1; positive integers → naturals ≥ 1 cast to ℝ, real powers Real.rpow; reason: 0-based indices; same instances
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 40, Proposition 5.8(iv)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- Proposition 5.8(iv), p. 40: with `p := p₁`, for all positive integers `x, y, z` with
`z = x + y − 1`, `x^{1−p} y^p ≤ F⋆_θ(x, y, z) ≤ x^{p₂} y^p`. -/
theorem proposition_5_8_iv (θ : Fin 3 → ℝ) (hθ : InTheta θ) (x y z : ℕ) (hx : 1 ≤ x)
    (hy : 1 ≤ y) (hz : z = x + y - 1) :
    (x : ℝ) ^ (1 - pExp θ 0) * (y : ℝ) ^ pExp θ 0 ≤ FstarTriple θ ![(x : ℝ), (y : ℝ), (z : ℝ)] ∧
      FstarTriple θ ![(x : ℝ), (y : ℝ), (z : ℝ)] ≤ (x : ℝ) ^ pExp θ 1 * (y : ℝ) ^ pExp θ 0 := by sorry

end MatMulPolyBarrier.Operational
