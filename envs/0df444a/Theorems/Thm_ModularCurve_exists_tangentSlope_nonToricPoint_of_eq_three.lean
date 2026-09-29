-- Prove2me | Theorems.Thm_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three
-- name    : ModularCurve.exists_tangentSlope_nonToricPoint_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/86abfc32-ab71-5129-9129-91bc75c0f6b2
-- title:
--   Tangent slope at the non-toric Tate slot point, p=3
-- statement:
--   Let $K$ be a commutative ring, let $p$ be a natural number with $p = 3$, let $\zeta \in K^\times$ satisfy $\zeta^p = 1$, and let $b, k$ be natural numbers with $1 \le k$ and $k \le p/2$ (so that $k = 1$). Write $E$ for the Weierstrass curve `tateBase K p` over the Laurent series ring $\mathrm{LaurentSeries}\,K$, obtained from the integral formal Tate curve `tatePowerSeries` by coefficient extension to Laurent series over $K$ followed by the ring homomorphism `qExpand K p`, which re-indexes a Hahn series along multiplication by $p$ on $\mathbb{Z}$ (i.e. substitutes $q \mapsto q^{p}$), and let $a_1, a_2, a_3, a_4$ be its coefficients. Write $(x, y) =$ `nonToricPoint K p (ζ ^ (b * k)) k`, the pair of Laurent series obtained by substituting the family `slotFamily K p (ζ ^ (b * k)) k` into the two explicit bivariate integral power series `tateUnivX` and `tateUnivY` (whose coefficients are given by the divisor sums displayed in their definitions) and regarding the results as Laurent series. The assertion is twofold: first, $2y + a_1 x + a_3$ is a unit in $\mathrm{LaurentSeries}\,K$; second, there is a Laurent series $\ell$ with $\ell\,(2y + a_1 x + a_3) = 3x^2 + 2a_2 x + a_4 - a_1 y$ and $\ell^2 + a_1 \ell - a_2 - 2x = x$.
--
--   This is the formal-series form of the statement that the non-toric slot point $P$ on the Tate curve at level $p = 3$ has invertible tangent denominator and that the duplication formula returns its own $x$-coordinate, $x(2P) = x(P)$, as is forced by $3P = O$. It is used in the verification that $P$ is a root of the division polynomial data for `tateBase K p`, in [`ModularCurve.eval_prePsi_tateBase_nonToricPoint_eq_zero`](thm.html#ModularCurve.eval_prePsi_tateBase_nonToricPoint_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_tangentSlope_nonToricPoint_of_eq_three
    (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (hp3 : p = 3)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ) (k : ℕ) (h1k : 1 ≤ k) (hkp : k ≤ p / 2) :
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
        = (nonToricPoint K p (ζ ^ (b * k)) k).1 := by sorry
