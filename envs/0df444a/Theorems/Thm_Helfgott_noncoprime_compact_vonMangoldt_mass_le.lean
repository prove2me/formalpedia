-- Prove2me | Theorems.Thm_Helfgott_noncoprime_compact_vonMangoldt_mass_le
-- name    : Helfgott.noncoprime_compact_vonMangoldt_mass_le
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T07:06:14.637031+00:00
-- url     : https://prove2.me/theorems/a15986a2-56e3-4113-9048-cf04fe5fa69d
-- title:
--   Sharp compact von Mangoldt mass bound for indices sharing a prime with the modulus
-- statement:
--   Let $q>0$ and $K$ be natural numbers. Let $w_n$ be real weights supported on $n<2^K$, with $|w_n|\le A$ there and $A\ge0$. Then
--
--   $$\sum_{\substack{n\ge0\\(n,q)>1}}\Lambda(n)|w_n|\le AK\log q.$$
--
--   The bound retains every prime power in the support, including repeated prime factors of the modulus. It controls the non-coprime coefficient mass in the complete rational Dirichlet expansion for compact smoothing coefficients. Infinite Gaussian smoothing tails require a separate estimate.
-- source:
--   The elementary divisor identity for the von Mangoldt function, proved in Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt. Applied to the non-coprime remainder in Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
open scoped BigOperators
open Finset

theorem Helfgott.noncoprime_compact_vonMangoldt_mass_le (q K : ℕ) (hq : 0<q)
    (w : ℕ → ℝ) (A : ℝ) (hA : 0≤A) (hw : ∀ n<2^K,|w n|≤A)
    (hzero : ∀ n,2^K≤n → w n=0) :
    (∑' n : ℕ,if Nat.Coprime n q then (0:ℝ) else
      ArithmeticFunction.vonMangoldt n*|w n|) ≤ A*(K:ℝ)*Real.log (q:ℝ) := by sorry
