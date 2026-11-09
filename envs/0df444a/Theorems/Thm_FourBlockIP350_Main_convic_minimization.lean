-- Prove2me | Theorems.Thm_FourBlockIP350_Main_convic_minimization
-- name    : FourBlockIP350.Main.convic_minimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:44.294091+00:00
-- url     : https://prove2.me/theorems/08ff4281-609a-4a88-b8f0-dba2c18ee5c4
-- title:
--   Theorem 2.9 — Comparison-oracle discrete convic minimization
-- statement:
--   One comparison-oracle algorithm minimizes every discrete convic real-valued function on the full Euclidean-ball lattice domain $B_\rho\cap\mathbb Z^d$, for $d\ge1$ and $\rho\ge0$. It outputs an integer point attaining the minimum. For absolute constants $C,c,e>0$, its numbers of queries and additional arithmetic operations are bounded separately by
--   $$C2^{cd^2\lceil\log_2(d+1)\rceil}\log_2(2+\rho),\qquad
--   C2^{cd^2\lceil\log_2(d+1)\rceil}(\log_2(2+\rho))^e.$$
--   Every query is required to belong to that entire ball-domain. Only comparisons are obtained from the oracle, and the result holds for every oracle with the stated answers on the domain.
--
--   This is an arithmetic-operation and query bound. It does not assign unit binary cost to real arithmetic or to implementing a comparison.
--
--   Differences from the source:
--   - encoding: an algorithm with separate 2^{O(d² log(d+1))} query and arithmetic bounds → one finite arithmetic/comparison program; positive absolute C,c,e; explicit log base 2 and ceiling in the dimension factor; reason: rounding and log bases alter only uniform hidden constants; the input radius remains an arbitrary nonnegative real and arithmetic is kept separate from bit complexity
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 6, Theorem 2.9

import Mathlib
import Definitions.Def_FourBlockIP350_Main_OracleMachine

namespace FourBlockIP350.Main

open scoped BigOperators

theorem convic_minimization :
    ∃ P : OracleProgram, ∃ C c e : ℕ, 0 < C ∧ 0 < c ∧ 0 < e ∧
    ∀ d : ℕ, 0 < d → ∀ ρ : ℝ, 0 ≤ ρ → ∀ h : ZVec d → ℝ,
      DiscreteConvic (BallLattice d ρ) h →
      ∀ O : RVec d → RVec d → Ordering, ComparisonOracle ρ h O →
      ∃ t : ℕ, ∃ a : Address, ∃ z : ZVec d,
        OraclePrefixValid d ρ P O t ∧
        P[(oracleState d ρ P O t).pc]? = some (.halt a) ∧
        pointAt d (oracleState d ρ P O t) a = realVec z ∧
        z ∈ BallLattice d ρ ∧ (∀ w ∈ BallLattice d ρ, h z ≤ h w) ∧
        (queryCount d ρ P O t : ℝ) ≤
          C * (2 : ℝ) ^ (c * d^2 * Nat.clog 2 (d+1)) * Real.logb 2 (2+ρ) ∧
        (arithmeticCount d ρ P O t : ℝ) ≤
          C * (2 : ℝ) ^ (c * d^2 * Nat.clog 2 (d+1)) * (Real.logb 2 (2+ρ))^e := by sorry

end FourBlockIP350.Main
