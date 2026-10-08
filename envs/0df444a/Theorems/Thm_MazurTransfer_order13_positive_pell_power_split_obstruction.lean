-- Prove2me | Theorems.Thm_MazurTransfer_order13_positive_pell_power_split_obstruction
-- name    : MazurTransfer.order13_positive_pell_power_split_obstruction
-- status  : Open
-- author  : @Vas
-- created : 2026-10-07T18:52:39.468992+00:00
-- url     : https://prove2.me/theorems/9bf2bc16-ce14-4196-85b1-e6ddd105a0b6
-- title:
--   Order13: exclusion of the primitive positive Pell power-split cover
-- statement:
--   Let $F(a,b)=a^6+2a^5b+a^4b^2+2a^3b^3+6a^2b^4+4ab^5+b^6$. Let $H(a,b)$ and $K(a,b)$ be the fixed degree-19 and degree-16 homogeneous Pell polynomials in the accompanying definitions, and put $P=H+cK$, $N=cK-H$. There are no integers $m,n,a,b,c,r,s$ with $n,a,b,c,r,s>0$, coprime pairs $(m,n),(a,b),(c,b),(r,s)$, odd $m,n$, $-n<m<n$, and all of the following relations:
--   \[
--   \begin{aligned}
--   n^2-m^2&=4ab(a+b),\\
--   m^2+4mn-n^2&=4(a^3-3ab^2-b^3),\\
--   2m^2-4mn-2n^2&=4(-a^3-3a^2b+b^3),\\
--   19&\nmid 3a-2b,\\
--   2c&=m^2+n^2,\qquad c^2=F(a,b),\\
--   P&=2r^{38},\qquad N=2s^{38},\qquad b=rs.
--   \end{aligned}
--   \]
--   This is the exact remaining integer arithmetic obligation in the checked positive-chamber reduction of the order-13 genus-two rational-point problem. A proof supplies the unchanged unconditional order-13 exclusion; neither this statement nor the reduction assumes a rank computation or a rational-point classification.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, XOneThirteenDescent, XOneThirteenPositivePell and XOneThirteenPellPowerSplit. Original typed dependencies and complete Lean declaration ranges preserve Apache-2.0 provenance. The conjugate-prime condition is restated using the original checked equivalence SixthRootPiConjDivides (a,b) iff 19 divides 3*a-2*b. Named downstream consumer: MazurTransfer.order13_no_noncuspidal_genus_two_point, whose full unconditional rational sextic statement is unchanged. This obligation remains Open until its arithmetic is actually proved.

import Mathlib
import Definitions.Def_MazurTransfer_Order13PositivePellCoverData

theorem MazurTransfer.order13_positive_pell_power_split_obstruction
    (m n a b c r s : ℤ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : 0 < r) (hs : 0 < s)
    (hmn : IsCoprime m n) (hab : IsCoprime a b)
    (hcb : IsCoprime c b) (hrs : IsCoprime r s)
    (hmOdd : Odd m) (hnOdd : Odd n)
    (hbetween : -n < m ∧ m < n)
    (hlead : n ^ 2 - m ^ 2 = 4 * (a * b * (a + b)))
    (htrace : m ^ 2 + 4 * m * n - n ^ 2 =
      4 * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3))
    (hpair : 2 * m ^ 2 - 4 * m * n - 2 * n ^ 2 =
      4 * (-a ^ 3 - 3 * a ^ 2 * b + b ^ 3))
    (hpi : ¬ (19 : ℤ) ∣ 3 * a - 2 * b)
    (htwice : 2 * c = m ^ 2 + n ^ 2)
    (hcurve : c ^ 2 = MazurTorsion.XOneThirteenDescent.integerSexticHomogeneous a b)
    (hplus : MazurTorsion.XOneThirteenDescent.positivePellFactor a b c = 2 * r ^ 38)
    (hminus : MazurTorsion.XOneThirteenDescent.negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s) : False := by sorry
