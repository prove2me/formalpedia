-- Prove2me | Theorems.Thm_GRH_liouville_partial_sum_reduced_progression_power_bound
-- name    : GRH.liouville_partial_sum_reduced_progression_power_bound
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T00:25:27.284817+00:00
-- url     : https://prove2.me/theorems/590f5772-3617-4188-a7da-2c20e66541b2
-- title:
--   Square-root-scale cancellation of the Liouville function in fixed reduced progressions
-- statement:
--   Let $q\ge1$ be fixed and $1/2<\sigma<1$. Write $\lambda(n)=(-1)^{\Omega(n)}$, where $\Omega(n)$ counts prime factors with multiplicity. The conjectural bound asserts that a constant $C=C(q,\sigma)\ge0$ exists such that, uniformly for all units $a\bmod q$ and all nonnegative integers $N$,
--   $$\left|\sum_{1\le n\le N,\ n\equiv a\bmod q}\lambda(n)\right|\le C(N+1)^\sigma.$$
--   This is an open arithmetic cancellation estimate. The square-divisor transfer shows its role in bounding the corresponding Möbius sums in the campaign.
-- source:
--   NIST Digital Library of Mathematical Functions, §27.2, https://dlmf.nist.gov/27.2 , for the Liouville function; the asserted fixed-progression cancellation is an open GRH-strength input to the square-divisor reduction. For the related conditional Möbius bounds see L. Ye, Bounding sums of the Möbius function over arithmetic progressions, https://arxiv.org/abs/1406.7326 .

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open ArithmeticFunction Finset
namespace GRH

theorem liouville_partial_sum_reduced_progression_power_bound
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ j ∈ range (N+1), if (j:ZMod q)=a then (liouville j:ℝ) else 0| ≤ C*((N:ℝ)+1)^σ := by sorry

end GRH
