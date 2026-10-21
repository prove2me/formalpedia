-- Prove2me | Theorems.Thm_FunctionField_genus_eq_genusChart
-- name    : FunctionField.genus_eq_genusChart
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T13:41:10.370523+00:00
-- url     : https://prove2.me/theorems/56ca41d0-5b74-498e-8ec5-bbde83c83af8
-- title:
--   The intrinsic genus of a function field equals its genus computed on the $k(X)$-chart
-- statement:
--   Let $k$ be a field and let $K/k$ be an algebraic function field in one variable, presented through a separating variable: $K$ is a finite separable extension of the rational function field $k(X)$, the structure maps $k\to k[X]\to k(X)\to K$ being compatible. Assume that $k$ is the full constant field of $K$: every element of $K$ that is algebraic over $k$ already lies in $k$.
--
--   A *place* $P$ of $K/k$ is a valuation ring $\mathcal O_P$ with $k\subseteq\mathcal O_P\subsetneq K$ whose value group is infinite cyclic; $v_P:K^\times\to\mathbb Z$ is its normalized valuation and $\deg P=[\mathcal O_P/\mathfrak m_P:k]$ its degree. A *divisor* is a finite formal sum $D=\sum_P n_P\,P$ with $n_P\in\mathbb Z$, of degree $\deg D=\sum_P n_P\deg P$. Its Riemann–Roch space is
--   $$\mathcal L(D)=\{f\in K:\ f=0\ \text{or}\ v_P(f)\ge -n_P\ \text{for every place } P\},$$
--   a $k$-vector space of dimension $\ell(D)$. The *genus* $g$ of $K/k$ is the largest value of the defect $\deg D+1-\ell(D)$ over all divisors $D$.
--
--   The same quantities can be computed in the two-chart presentation of $K$ over $k(X)$: the *coordinate places* are the nonzero primes of the integral closure of $k[X]$ in $K$ and the nonzero primes of the integral closure in $K$ of the valuation ring at infinity $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$; a coordinate divisor is a finite formal sum of coordinate places, its degree weights each place by the $k$-dimension of its residue field, and $\ell$ is computed with the adic valuations of these primes. The *chart genus* $g_{\mathrm{chart}}(K)$ is the maximum of $\deg D+1-\ell(D)$ over all coordinate divisors $D$. Then
--   $$g(K)=g_{\mathrm{chart}}(K).$$
--
--   This identifies the coordinate-free genus with the genus computed by the chart-based proofs of the library, so that the Riemann–Roch theorem and its corollaries can be stated for intrinsic divisors.
--
--   **Formalization Note** The tower $k\to k[X]\to k(X)\to K$ is given by the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `Algebra k K`, `IsScalarTower k k[X] K` and `IsScalarTower k[X] k⟮X⟯ K`, together with `FunctionField k K` ($K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`. The full constant field hypothesis is `IsFullConstantField k K`. Places (`FunctionField.Place k K`) are valuation subrings $\mathcal O\neq K$ containing the image of $k$ whose value group admits an order isomorphism with $\mathbb Z^{m0}$ (only its existence is recorded); the normalized valuation is written multiplicatively, $v(f)=e^{-v_P(f)}$, so that $f\in\mathcal L(D)$ reads $v(f)\le e^{n_P}$ for every place. Degrees of places and $\ell(D)$ are `Module.finrank` over $k$, and divisors are finitely supported functions from places to $\mathbb Z$. The genus `FunctionField.genus k K` is defined as the natural-number truncation of the supremum in $\mathbb Z$ of the defects $\deg D+1-\ell(D)$. The chart genus `FunctionField.Chart.genus k K` is the natural number chosen as the maximal defect of coordinate divisors `DivisorA k K` (its existence is a separate result of the library). The statement therefore also says that the supremum defining the intrinsic genus equals this maximum.
-- source:
--   Auxiliary comparison lemma of the formalization; both sides are the genus of H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Definition 1.4.15, in two presentations of the places. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/RiemannRoch.lean#L139-L157

import Mathlib
import Definitions.Def_RiemannRoch_WeilDifferentials
/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/

open scoped nonZeroDivisors Polynomial RatFunc WithZero
open FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

theorem FunctionField.genus_eq_genusChart : genus k K = Chart.genus k K := by sorry
