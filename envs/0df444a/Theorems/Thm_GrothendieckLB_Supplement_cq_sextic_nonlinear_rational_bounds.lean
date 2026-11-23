-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_sextic_nonlinear_rational_bounds
-- name    : GrothendieckLB.Supplement.cq_sextic_nonlinear_rational_bounds
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T17:50:31.445091+00:00
-- url     : https://prove2.me/theorems/d298d7e6-d2fe-4567-992f-555081641f9e
-- title:
--   Rational bounds on the nonlinear finite Hermite sums
-- statement:
--   Let $M_k$ have the three prescribed dyadic starting intervals, odd entries zero and the sextic moment recurrence through the indicated finite cutoff. For either square root $s$ of the rational squared slope and the polynomial $P_{ab}$ in the sextic reduction, put $L_M(x^k)=M_k$ and extend linearly. If $m=2j+3$ and $0\le j<125$, the unnormalized Hermite sum satisfies
--   $$
--   \left|\sum_{a+b\le m}\frac{(-1)^bL_M(P_{ab})^2}{a!b!}[t^{m-b}]\rho(t)^a\right|
--   \le 2(3.14159265358979323846)\,u_j10^{-20},
--   $$
--   where $u_j$ is the published integer upper endpoint. Each squared polynomial moment is independent of the choice of sign for $s$. This finite assertion involves only algebraic arithmetic; its rational prefactor suffices for division by $2\pi$ in the Taylor formula.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Theorem 5.1 and Appendix C.1; sextic polynomial moment reduction.

import Definitions.Def_GrothendieckLB_Supplement_cqSexticHead
import Definitions.Def_GrothendieckLB_Supplement_cqHeadUnits

namespace GrothendieckLB.Supplement

theorem cq_sextic_nonlinear_rational_bounds (M : ℕ → ℝ) (hseed : cqSexticSeedBounds M)
    (hodd : ∀ n, n ≤ 757 → Odd n → M n = 0)
    (hrec : let c : ℝ := 0.136419125^2 / (6*(1+(0.34101124:ℝ)^2+0.05276111^2))
      ∀ n : ℕ, n ≤ 751 → 3*c*M (n+6) =
        ((n:ℝ)+1)*M n - (1+9*c)*M (n+2) + 12*c*M (n+4))
    (s : ℝ) (hs : s^2 = 0.136419125^2 / (6*(1+(0.34101124:ℝ)^2+0.05276111^2))) :
    ∀ j : ℕ, j < 125 →
      let m := 2*j+3
      |∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
        (-1:ℝ)^b * ((cqSexticPoly s a b).sum (fun k c => c*M k))^2 /
          ((a.factorial:ℝ)*(b.factorial:ℝ)) *
          ((cqRhoPoly 0.34101124 0.05276111)^a).coeff (m-b)| ≤
        (2*3.14159265358979323846)*(((cqHeadUnits[j]?.getD 0 : ℕ):ℝ)/10^20) := by sorry

end GrothendieckLB.Supplement
