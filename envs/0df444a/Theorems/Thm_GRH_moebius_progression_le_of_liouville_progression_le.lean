-- Prove2me | Theorems.Thm_GRH_moebius_progression_le_of_liouville_progression_le
-- name    : GRH.moebius_progression_le_of_liouville_progression_le
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:25:26.802451+00:00
-- url     : https://prove2.me/theorems/ed342a94-f581-487e-a655-dd5a9b0ff82e
-- title:
--   A uniform Liouville bound transfers to Möbius sums in reduced progressions with explicit constant
-- statement:
--   Let $q$ be a positive integer, let $\sigma>1/2$, and let $C\ge0$. Write $L(N;q,a)$ and $M(N;q,a)$ for the sums of the Liouville and Möbius functions, respectively, over positive integers at most $N$ congruent to $a$ modulo $q$. Assume $|L(N;q,a)|\le C(N+1)^\sigma$ for every reduced residue class $a$ and every nonnegative integer $N$. Then the explicit bound
--   $$|M(N;q,a)|\le 2^\sigma\zeta(2\sigma)C(N+1)^\sigma$$
--   holds uniformly over the same classes and cutoffs. The convergence threshold comes from the correction for square divisors and requires no further cancellation in those divisors.
-- source:
--   The arithmetic functions are as in NIST Digital Library of Mathematical Functions, §27.2, https://dlmf.nist.gov/27.2 . The explicit uniform transfer factor here is obtained by square-divisor inversion and summing the resulting positive majorant.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open ArithmeticFunction Finset
namespace GRH

theorem moebius_progression_le_of_liouville_progression_le (q : ℕ) [NeZero q] (σ C : ℝ) (hσ : 1/2 < σ) (hC : 0 ≤ C)
    (H : ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ j ∈ range (N+1), if (j:ZMod q)=a then (liouville j:ℝ) else 0| ≤ C*((N:ℝ)+1)^σ)
    (a : ZMod q) (ha : IsUnit a) (N : ℕ) :
    |∑ k ∈ range (N+1), if (k:ZMod q)=a then (moebius k:ℝ) else 0| ≤
      (C * (2:ℝ)^σ * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹) * ((N:ℝ)+1)^σ := by sorry

end GRH
