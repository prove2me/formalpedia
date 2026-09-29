-- Prove2me | Theorems.Thm_ModularCurve_exists_chordSlope_nonToricPoint
-- name    : ModularCurve.exists_chordSlope_nonToricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/e7c5fbef-bd8a-5c07-9efb-1bd1db723fa3
-- title:
--   Chord relation for non-toric Tate slot points
-- statement:
--   Let $K$ be a commutative ring, $p$ a prime with $p \ge 5$, and $\zeta \in K^{\times}$ a unit with $\zeta^{p} = 1$; let $b, i, j, m$ be natural numbers subject to $1 \le i$, $1 \le j$, $i \neq j$, $i \le p/2$, $j \le p/2$ (floor division), $1 \le m \le p/2$, and $m = i + j$ or $i + j + m = p$. For a unit $c$ and an index $k$, `nonToricPoint K p c k` is the pair of Laurent series over $K$ obtained by viewing as Hahn series the two power series `slotSubst K p c k tateUnivX` and `slotSubst K p c k tateUnivY`, i.e. the substitution of the family `slotFamily K p c k` into the two-variable integral power series `tateUnivX`, `tateUnivY`, whose coefficient at an exponent $e$ is given by the divisor sums $-2\sum_{d \mid e_1} d$ resp. $\sum_{d \mid e_1} d$ when $e_0 = e_1$, and otherwise by $|e_0 - e_1|$ resp. $\pm\binom{\cdot}{2}$ according as $|e_0 - e_1|$ divides $e_1$ or not. Write $(x_k, y_k)$ for `nonToricPoint K p (ζ ^ (b * k)) k`, and let $a_1, a_2$ be the first two coefficients of the Weierstrass curve `tateBase K p` over $K((q))$, obtained from the integral Tate power-series model by base change to $K$ followed by the exponent-scaling homomorphism `qExpand K p`. The assertion is that $x_i - x_j$ is a unit of $K((q))$ and that there exists a Laurent series $\ell$ with $\ell\,(x_i - x_j) = y_i - y_j$ and $\ell^{2} + a_1 \ell - a_2 - x_i - x_j = x_m$.
--
--   This expresses that the Tate parametrisation is additive on the non-toric $p$-torsion slots, in the form of the chord construction: the line through the slot points of exponents $i$ and $j$ meets `tateBase K p` again above the slot of exponent $m$, where $m \equiv \pm(i+j) \bmod p$ is the representative in $[1, p/2]$, and the identity holds as an identity of Laurent series over an arbitrary commutative coefficient ring. It feeds the computations at the cusp, being used by [`ModularCurve.eval_prePsi_tateBase_nonToricPoint_eq_zero`](thm.html#ModularCurve.eval_prePsi_tateBase_nonToricPoint_eq_zero), [`ModularCurve.inLine_cuspData_smul_of_five_le`](thm.html#ModularCurve.inLine_cuspData_smul_of_five_le) and [`ModularCurve.isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le`](thm.html#ModularCurve.isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_chordSlope_nonToricPoint.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_chordSlope_nonToricPoint
    (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ) (i j m : ℕ)
    (h1i : 1 ≤ i) (h1j : 1 ≤ j) (hij : i ≠ j) (hip : i ≤ p / 2) (hjp : j ≤ p / 2)
    (h1m : 1 ≤ m) (hmp : m ≤ p / 2) (hm : m = i + j ∨ i + j + m = p) :
    IsUnit ((nonToricPoint K p (ζ ^ (b * i)) i).1 - (nonToricPoint K p (ζ ^ (b * j)) j).1) ∧
    ∃ ℓ : LaurentSeries K,
      ℓ * ((nonToricPoint K p (ζ ^ (b * i)) i).1 - (nonToricPoint K p (ζ ^ (b * j)) j).1)
        = (nonToricPoint K p (ζ ^ (b * i)) i).2 - (nonToricPoint K p (ζ ^ (b * j)) j).2 ∧
      ℓ ^ 2 + (tateBase K p).a₁ * ℓ - (tateBase K p).a₂
          - (nonToricPoint K p (ζ ^ (b * i)) i).1 - (nonToricPoint K p (ζ ^ (b * j)) j).1
        = (nonToricPoint K p (ζ ^ (b * m)) m).1 := by sorry
