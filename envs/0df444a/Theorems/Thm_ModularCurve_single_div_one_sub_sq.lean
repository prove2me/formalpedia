-- Prove2me | Theorems.Thm_ModularCurve_single_div_one_sub_sq
-- name    : ModularCurve.single_div_one_sub_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/961d3039-65ac-5acc-ae8b-171b4f880bba
-- title:
--   Closed form for cq^j/(1-cq^j)² in K((q))
-- statement:
--   Let $K$ be a field, let $j$ be a natural number with $j > 0$, and let $c \in K$. Work in the field of formal Laurent series `LaurentSeries K`, realised as Hahn series over $\mathbb{Z}$ with coefficients in $K$, and let `HahnSeries.single (j : ℤ) c` denote the monomial $c q^{j}$, i.e. the series whose coefficient in degree $j$ is $c$ and whose other coefficients vanish. The assertion is the identity
--   $$\frac{c q^{j}}{\bigl(1 - c q^{j}\bigr)^{2}} \;=\; \sum_{n \ge 0} a_n q^{n},$$
--   where the right-hand side is the image under `HahnSeries.ofPowerSeries ℤ K` of the formal power series in `PowerSeries K` whose $n$-th coefficient $a_n$ is the image in $K$ of the natural number $n/j$ times $c^{n/j}$ (natural-number division) when $j$ divides $n$, and is $0$ otherwise; equivalently the right-hand side is $\sum_{m \ge 0} m\, c^{m} q^{jm}$. The quotient on the left is the division in the field `LaurentSeries K`, and positivity of $j$ is what makes $1 - c q^{j}$ a unit there, its constant term being $1$.
--
--   This is the generating-function identity $\sum_{m \ge 0} m u^{m} = u/(1-u)^{2}$ specialised to the monomial $u = c q^{j}$ and recorded as an equality of Laurent series in $q$. It supplies the $q$-expansion of the leading term of the $x$-coordinate of a point on the Tate curve with parameter $c q^{j}$, and is used in the verification of the Tate curve equation ([`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation)) and of the equation satisfied by the corresponding torsion-type point ([`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_single_div_one_sub_sq.lean

import Mathlib.RingTheory.LaurentSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.single_div_one_sub_sq (K : Type*) [Field K] (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 2 =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => if j ∣ n then ((n / j : ℕ) : K) * c ^ (n / j) else 0) := by sorry
