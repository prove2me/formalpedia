-- Prove2me | Theorems.Thm_ModularCurve_exists_tangentSlope_nonToricPoint
-- name    : ModularCurve.exists_tangentSlope_nonToricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/a68e3f44-b912-5384-b500-5af3cf6675de
-- title:
--   Tangent doubling law at non-toric slot points
-- statement:
--   Let $K$ be a commutative ring, $p$ a prime with $5 \le p$, and $\zeta \in K^{\times}$ a unit with $\zeta^{p} = 1$; let $b, k, m$ be natural numbers with $1 \le k \le p/2$ and $1 \le m \le p/2$ (natural division), and suppose that $m = 2k$ or $2k + m = p$. Write $(x_j(c), y_j(c)) =$ `nonToricPoint K p c j`, the pair of Laurent series over $K$ obtained by substituting the family `slotFamily K p c j` into the two-variable integral power series `tateUnivX`, `tateUnivY` (whose coefficients at an exponent $e$ are given by the explicit divisor sums and binomial coefficients displayed in their definitions) and viewing the results in $K((q))$ via `HahnSeries.ofPowerSeries`. Let $a_1, a_2, a_3, a_4$ be the coefficients of the Weierstrass curve `tateBase K p`, the base change of the integral Tate curve to $K((q))$ followed by the exponent-scaling ring homomorphism `qExpand K p`, which multiplies all Hahn exponents by $p$. Then, with $x_k = x_k(\zeta^{bk})$ and $y_k = y_k(\zeta^{bk})$, the element $2y_k + a_1 x_k + a_3$ is a unit of $K((q))$, and there exists $\ell \in K((q))$ with $\ell\,(2y_k + a_1 x_k + a_3) = 3x_k^{2} + 2a_2 x_k + a_4 - a_1 y_k$ and $\ell^{2} + a_1 \ell - a_2 - 2x_k = x_m(\zeta^{bm})$.
--
--   This is the duplication law of the Tate parametrisation read off on the family of non-toric $p$-torsion slot points: the tangent at the $k$-th slot point is defined (its denominator is a unit, so the slope $\ell$ exists and is determined) and its third intersection with the curve has the $x$-coordinate of the slot point indexed by $2k$ folded back into the range $[1, p/2]$, the folding being recorded by the alternative $m = 2k$ or $2k + m = p$. It feeds the computations with tangents and chords at the slot points, for instance the vanishing of `prePsi` evaluated at these points and the unit statements used for the cusp data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_tangentSlope_nonToricPoint.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_tangentSlope_nonToricPoint
    (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ) (k m : ℕ)
    (h1k : 1 ≤ k) (hkp : k ≤ p / 2)
    (h1m : 1 ≤ m) (hmp : m ≤ p / 2) (hm : m = 2 * k ∨ 2 * k + m = p) :
    IsUnit (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
        + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃) ∧
    ∃ ℓ : LaurentSeries K,
      ℓ * (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
          + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃)
        = 3 * (nonToricPoint K p (ζ ^ (b * k)) k).1 ^ 2
          + 2 * (tateBase K p).a₂ * (nonToricPoint K p (ζ ^ (b * k)) k).1
          + (tateBase K p).a₄ - (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).2 ∧
      ℓ ^ 2 + (tateBase K p).a₁ * ℓ - (tateBase K p).a₂
          - 2 * (nonToricPoint K p (ζ ^ (b * k)) k).1
        = (nonToricPoint K p (ζ ^ (b * m)) m).1 := by sorry
