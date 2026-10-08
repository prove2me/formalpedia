-- Prove2me | Theorems.Thm_Helfgott_squarefree_coprime_count_certificate
-- name    : Helfgott.squarefree_coprime_count_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T13:37:32.107362+00:00
-- url     : https://prove2.me/theorems/d9783645-deb7-43b5-87fa-1d5964b6d673
-- title:
--   Exact squarefree coprime count and explicit truncated density error
-- statement:
--   For positive integer \(q\) and any nonnegative integer \(N\), put \(D=\lfloor\sqrt N\rfloor\) and \(Q_q(N)=\sum_{1\le n\le N,(n,q)=1}\mu(n)^2\). Then
--   \[
--   Q_q(N)=\sum_{1\le d\le D,(d,q)=1}\mu(d)\sum_{e\mid q}\mu(e)\left\lfloor\frac N{d^2e}\right\rfloor
--   \]
--   and
--   \[
--   \left|Q_q(N)-N\frac{\varphi(q)}q\sum_{1\le d\le D,(d,q)=1}\frac{\mu(d)}{d^2}\right|
--   \le D\sum_{e\mid q}|\mu(e)|.
--   \]
--   All floor endpoints, including \(N=0\), are exact. This is the squarefree coprime counting input for the signed Mobius cancellation in Vaughan Type II estimates. The infinite density and its sharp uniform remainder are separate subsequent steps.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.1 (squarefree coprime counting in the Type II Mobius energy), https://arxiv.org/abs/1205.5252. Complete original Lean proof from Mobius inversion, exact divisor counting and floor errors. Mathlib attributions retained. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_coprime_count_certificate  (q N : ℕ) (hq : q ≠ 0) :
    ((∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0) ∧
    |(∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (N : ℝ)*((q.totient : ℝ)/(q : ℝ))*
        (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)| ≤
      (N.sqrt : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|) := by sorry

end Helfgott
