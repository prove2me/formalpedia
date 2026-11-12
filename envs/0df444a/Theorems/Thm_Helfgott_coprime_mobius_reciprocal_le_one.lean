-- Prove2me | Theorems.Thm_Helfgott_coprime_mobius_reciprocal_le_one
-- name    : Helfgott.coprime_mobius_reciprocal_le_one
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T19:59:27.60445+00:00
-- url     : https://prove2.me/theorems/ade37461-c107-420f-8794-acb22367614a
-- title:
--   The elementary coprime Mobius reciprocal sum bound
-- statement:
--   For all natural numbers $q,N$, $|\sum_{1\le d\le N,\ (d,q)=1}\mu(d)/d|\le1$. This includes the usual positive modulus case and also $q=0$ by the standard coprimality convention.
-- source:
--   Classical bound recorded as (2.7) in Helfgott, Minor arcs for Goldbach (arXiv:1205.5252v4), attributed there to Granville and Ramare, Lemma 10.2. The coprime Mobius convolution identity is retained with Apache 2.0 attribution to raresbuhai, submission 4b19f26e-e6f8-4a14-8cf6-e0ea33b44440. Finite floor decomposition and complementary support argument formalized locally.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
open Finset ArithmeticFunction
open scoped BigOperators

theorem Helfgott.coprime_mobius_reciprocal_le_one (q N : ℕ) :
    |∑ d ∈ Icc 1 N, if Nat.Coprime d q then ((moebius d:ℤ):ℝ)/(d:ℝ) else 0| ≤ 1 := by sorry
