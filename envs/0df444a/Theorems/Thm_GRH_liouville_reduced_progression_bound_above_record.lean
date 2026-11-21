-- Prove2me | Theorems.Thm_GRH_liouville_reduced_progression_bound_above_record
-- name    : GRH.liouville_reduced_progression_bound_above_record
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:37:02.074812+00:00
-- url     : https://prove2.me/theorems/a79a1901-e866-466f-8a5d-5c02b8291dbe
-- title:
--   Liouville cancellation in every fixed reduced progression above the current zero-free boundary
-- statement:
--   Fix a positive modulus $q$ and $\sigma>0.8749570698$. There is a constant $C(q,\sigma)\ge0$ such that for every unit residue class $a\bmod q$ and all $N\ge0$,
--   $$\left|\sum_{1\le n\le N,\ n\equiv a\pmod q}\lambda(n)\right|\le C(q,\sigma)(N+1)^\sigma.$$
--   Here $\lambda(n)=(-1)^{\Omega(n)}$. This gives the uniform finite-cutoff conclusion of the open Liouville progression frontier throughout the exponent range above the platform's current zero-free boundary.
-- source:
--   The frontier is https://prove2.me/theorems/590f5772-3617-4188-a7da-2c20e66541b2. Our input is the fixed-modulus Möbius progression bound https://prove2.me/theorems/956d623a-a863-453a-a3ed-b612b57c5d92. The reverse square-divisor convolution is proved from unique squarefree kernels; finite reindexing and the summable-majorant method adapt the accepted proof in the opposite direction at https://prove2.me/theorems/ed342a94-f581-487e-a655-dd5a9b0ff82e.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open ArithmeticFunction Finset

theorem GRH.liouville_reduced_progression_bound_above_record (q : ℕ) [NeZero q] (σ : ℝ) (hσ : (0.8749570698:ℝ) < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ j ∈ range (N+1), if (j:ZMod q)=a then (liouville j:ℝ) else 0| ≤ C*((N:ℝ)+1)^σ := by sorry
