-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_proposition_5_8_ii
-- name    : MatMulPolyBarrier.Operational.proposition_5_8_ii
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:20.209078+00:00
-- url     : https://prove2.me/theorems/12c9cb66-6517-43f2-a256-b5e0224958cf
-- title:
--   Proposition 5.8(ii) — $y\mapsto F^\star_\theta(x,y,x+y-1)^{1/p}$ is concave on $\mathbb Z_{\ge1}$
-- statement:
--   Let $\theta\in\Theta$ and $p:=p_1=\theta_1(1-\theta_2)^{-1}(1-\theta_3)^{-1}$. For every positive integer $x$, the function $g(y):=F^\star_\theta(x,y,x+y-1)^{1/p}$ on $\mathbb Z_{\ge1}$ is concave, that is,
--   $$g(y)+g(y+2)\le 2\,g(y+1)\qquad\text{for every integer }y\ge1.$$
--   This is the inequality behind (D3) in the proof of Proposition 5.9.
--
--   Differences from the source:
--   - encoding: "y ↦ F⋆_θ(x, y, x+y−1)^{1/p} on Z≥1 is concave" → g(y) + g(y+2) ≤ 2 g(y+1) for every natural y ≥ 1; reason: concavity of a function on the integers is nonpositivity of its second differences; same instances
--   - encoding: p = p₁ → pExp θ 0; reason: 0-based indices
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 40, Proposition 5.8(ii)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- Proposition 5.8(ii), p. 40: with `p := p₁`, for every positive integer `x`, the function
`g(y) := F⋆_θ(x, y, x + y − 1)^{1/p}` on `ℤ_{≥1}` is concave, i.e. its second differences are
nonpositive: `g(y) + g(y + 2) ≤ 2 g(y + 1)` for every integer `y ≥ 1`. -/
theorem proposition_5_8_ii (θ : Fin 3 → ℝ) (hθ : InTheta θ) (x : ℕ) (hx : 1 ≤ x) (y : ℕ)
    (hy : 1 ≤ y) :
    FstarTriple θ ![(x : ℝ), (y : ℝ), (x : ℝ) + y - 1] ^ (1 / pExp θ 0) +
        FstarTriple θ ![(x : ℝ), (y : ℝ) + 2, (x : ℝ) + ((y : ℝ) + 2) - 1] ^
          (1 / pExp θ 0) ≤
      2 * FstarTriple θ ![(x : ℝ), (y : ℝ) + 1, (x : ℝ) + ((y : ℝ) + 1) - 1] ^
          (1 / pExp θ 0) := by sorry

end MatMulPolyBarrier.Operational
