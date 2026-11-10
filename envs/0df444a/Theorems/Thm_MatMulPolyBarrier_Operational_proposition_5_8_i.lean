-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_proposition_5_8_i
-- name    : MatMulPolyBarrier.Operational.proposition_5_8_i
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:14.20632+00:00
-- url     : https://prove2.me/theorems/feb5c87d-69f2-4009-9766-d48f66963ac3
-- title:
--   Proposition 5.8(i) — $\min(x,y)\le F^\star_\theta(x,y,x+y-1)\le x+y-1$, nondecreasing in $x$ and in $y$
-- statement:
--   Let $\theta\in\Theta$. For all positive integers $x,y,z$ with $z=x+y-1$,
--   $$\min(x,y)\le F^\star_\theta(x,y,z)\le z,$$
--   and $F^\star_\theta(x,y,x+y-1)$ is nondecreasing in $x$ and in $y$: for positive integers $x\le x'$ and $y\le y'$, $F^\star_\theta(x,y,x+y-1)\le F^\star_\theta(x',y,x'+y-1)$ and $F^\star_\theta(x,y,x+y-1)\le F^\star_\theta(x,y',x+y'-1)$. The upper bound gives (D1) and the monotonicity gives (R2) in the proof of Proposition 5.9.
--
--   Differences from the source:
--   - encoding: "nondecreasing in x and in y" over positive integers → x ≤ x' implies F(x, y, x+y−1) ≤ F(x', y, x'+y−1), and likewise in y, for positive integers; triples cast from ℕ to ℝ; reason: the definition of nondecreasing on the integers, same instances
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 40, Proposition 5.8(i)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- Proposition 5.8(i), p. 40: with `p := p₁`, for all positive integers `x, y, z` with
`z = x + y − 1`, `min(x, y) ≤ F⋆_θ(x, y, z) ≤ z`, and `F⋆_θ(x, y, x + y − 1)` is nondecreasing in
`x` and in `y` (over the positive integers). -/
theorem proposition_5_8_i (θ : Fin 3 → ℝ) (hθ : InTheta θ) :
    (∀ x y z : ℕ, 1 ≤ x → 1 ≤ y → z = x + y - 1 →
      min (x : ℝ) (y : ℝ) ≤ FstarTriple θ ![(x : ℝ), (y : ℝ), (z : ℝ)] ∧
      FstarTriple θ ![(x : ℝ), (y : ℝ), (z : ℝ)] ≤ (z : ℝ)) ∧
    (∀ x x' y : ℕ, 1 ≤ x → x ≤ x' → 1 ≤ y →
      FstarTriple θ ![(x : ℝ), (y : ℝ), (x : ℝ) + y - 1] ≤
        FstarTriple θ ![(x' : ℝ), (y : ℝ), (x' : ℝ) + y - 1]) ∧
    (∀ x y y' : ℕ, 1 ≤ x → 1 ≤ y → y ≤ y' →
      FstarTriple θ ![(x : ℝ), (y : ℝ), (x : ℝ) + y - 1] ≤
        FstarTriple θ ![(x : ℝ), (y' : ℝ), (x : ℝ) + y' - 1]) := by sorry

end MatMulPolyBarrier.Operational
