-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_proposition_5_8_iii
-- name    : MatMulPolyBarrier.Operational.proposition_5_8_iii
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:15.581625+00:00
-- url     : https://prove2.me/theorems/909a8c37-9ab0-4b6c-8c0a-b97c3fecdf10
-- title:
--   Proposition 5.8(iii) — $2F^\star_\theta(x,y,z)^{1/p}+F^\star_\theta(x,z,y)^{1/p}\le F^\star_\theta(x,2y+z,y+2z)^{1/p}$
-- statement:
--   Let $\theta\in\Theta$ and $p:=p_1$. For all positive integers $x,y,z$ with $z=x+y-1$,
--   $$2\,F^\star_\theta(x,y,z)^{1/p}+F^\star_\theta(x,z,y)^{1/p}\le F^\star_\theta(x,2y+z,y+2z)^{1/p}.$$
--   This is the inequality behind (D4) in the proof of Proposition 5.9.
--
--   Differences from the source:
--   - encoding: p = p₁ → pExp θ 0; positive integers x, y, z → naturals with 1 ≤ x, 1 ≤ y and z = x + y − 1 (so z ≥ 1), cast to ℝ; reason: 0-based indices and ℕ; same instances
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 40, Proposition 5.8(iii)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- Proposition 5.8(iii), p. 40: with `p := p₁`, for all positive integers `x, y, z` with
`z = x + y − 1`,
`2 F⋆_θ(x, y, z)^{1/p} + F⋆_θ(x, z, y)^{1/p} ≤ F⋆_θ(x, 2y + z, y + 2z)^{1/p}`. -/
theorem proposition_5_8_iii (θ : Fin 3 → ℝ) (hθ : InTheta θ) (x y z : ℕ) (hx : 1 ≤ x)
    (hy : 1 ≤ y) (hz : z = x + y - 1) :
    2 * FstarTriple θ ![(x : ℝ), (y : ℝ), (z : ℝ)] ^ (1 / pExp θ 0) +
        FstarTriple θ ![(x : ℝ), (z : ℝ), (y : ℝ)] ^ (1 / pExp θ 0) ≤
      FstarTriple θ ![(x : ℝ), 2 * (y : ℝ) + z, (y : ℝ) + 2 * z] ^ (1 / pExp θ 0) := by sorry

end MatMulPolyBarrier.Operational
