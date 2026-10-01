-- Prove2me | Theorems.Thm_HilbertSixteenth_cubic_two_algebraic_limit_cycles
-- name    : HilbertSixteenth.cubic_two_algebraic_limit_cycles
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:43:31.390983+00:00
-- url     : https://prove2.me/theorems/34ed4442-fad0-4d14-b8af-7372eff35e9c
-- title:
--   A cubic system with two algebraic limit cycles
-- statement:
--   Consider the cubic polynomial differential system
--   $$\dot x = 2y(10+xy),\qquad \dot y = 20x + y - 20x^3 - 2x^2y + 4y^3,$$
--   and the quartic curve $f(x,y)=2x^4-4x^2+4y^2+1=0$. The real curve $f=0$ consists of two ovals, one in the half-plane $x>0$ and one in $x<0$. Both ovals
--   $$\{f=0,\ x>0\}\quad\text{and}\quad\{f=0,\ x<0\}$$
--   are algebraic limit cycles of the system.
--
--   This shows that for non-generic invariant curves the bound of Theorem 4 (which is $1$ for $d=3$) can be exceeded, and gives $H_a(3)\ge2$, the value predicted by Conjecture 1.
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554, §7, example after Theorem 4 (Proposition 19 of J. Llibre, Y. Zhao, J. Phys. A 40 (2007) 14207–14222).

import Definitions.Def_HilbertSixteenth_PolyFields

namespace HilbertSixteenth
theorem cubic_two_algebraic_limit_cycles :
    let x : Poly2 := MvPolynomial.X 0
    let y : Poly2 := MvPolynomial.X 1
    let V : PolyField :=
      ⟨2 * y * (10 + x * y), 20 * x + y - 20 * x ^ 3 - 2 * x ^ 2 * y + 4 * y ^ 3⟩
    let f : Poly2 := 2 * x ^ 4 - 4 * x ^ 2 + 4 * y ^ 2 + 1
    IsAlgebraicLimitCycle V {p | p ∈ zeroSet f ∧ 0 < p.1} ∧
      IsAlgebraicLimitCycle V {p | p ∈ zeroSet f ∧ p.1 < 0} := by sorry
end HilbertSixteenth
