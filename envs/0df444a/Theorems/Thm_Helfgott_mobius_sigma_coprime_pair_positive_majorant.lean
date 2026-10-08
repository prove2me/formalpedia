-- Prove2me | Theorems.Thm_Helfgott_mobius_sigma_coprime_pair_positive_majorant
-- name    : Helfgott.mobius_sigma_coprime_pair_positive_majorant
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:04:50.546243+00:00
-- url     : https://prove2.me/theorems/b9331c09-c331-4d0a-9b37-f7493f88aaf9
-- title:
--   Positive transfer of any explicit Mobius partial-sum bound to the signed coprime pair sum
-- statement:
--   Let $\sigma(n)=\prod_{p\mid n}(p+1)$ and suppose $F(N)\ge|\sum_{1\le a\le N}\mu(a)/a|$ for all $0\le N\le Y$. Define $$T_F(Q,N)=\sum_{1\le e\le N\atop(e,Q)=1}\frac{\mu(e)^2}{e\sigma(e)}\sum_{1\le b\le N/e\atop p\mid b\Rightarrow p\mid eQ}\frac{F(\lfloor\lfloor N/e\rfloor/b\rfloor)}b.$$ Then for all $q,Y\ge0$, $$\left|\sum_{1\le r,t\le Y\atop(r,t)=(r,q)=(t,q)=1}\frac{\mu(r)\mu(t)}{\sigma(r)\sigma(t)}\right|\le\sum_{1\le d\le Y\atop(d,q)=1}\frac{|\mu(d)|}{\sigma(d)^2}T_F(dq,\lfloor Y/d\rfloor)^2.$$ This theorem propagates a separately proved unrestricted Mobius bound through all arithmetic reductions needed for Vaughan Type II cancellation.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equation (4.21), https://arxiv.org/abs/1205.5252. Complete finite Lean transfer theorem with explicit majorant hypothesis. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem mobius_sigma_coprime_pair_positive_majorant  (q Y : ℕ) (F : ℕ→ℝ)
    (hF : ∀ N≤Y,|∑ a∈Finset.Icc 1 N,((moebius a : ℤ) : ℝ)/(a : ℝ)|≤F N) :
    let sigma : ℕ→ℝ := fun n => ∏ p∈n.primeFactors,((p : ℝ)+1)
    let T : ℕ→ℕ→ℝ := fun Q N => ∑ e∈Finset.Icc 1 N,if Nat.Coprime e Q then
      (((moebius e : ℤ) : ℝ)^2/((e : ℝ)*sigma e))*
        (∑ b∈Finset.Icc 1 (N/e),if (∀ p∈b.primeFactors,p∣e*Q) then
          (1/(b : ℝ))*F ((N/e)/b) else 0) else 0
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
        (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t) else 0|≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(sigma d)^2)*(T (d*q) (Y/d))^2 else 0 := by sorry

end Helfgott
