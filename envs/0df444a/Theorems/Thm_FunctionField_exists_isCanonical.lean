-- Prove2me | Theorems.Thm_FunctionField_exists_isCanonical
-- name    : FunctionField.exists_isCanonical
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T13:47:49.208352+00:00
-- url     : https://prove2.me/theorems/8303fcc7-c09a-4a73-8d0e-9ea0d4dd0fc2
-- title:
--   Existence of a canonical divisor of an algebraic function field
-- statement:
--   Let $k$ be a field and let $K/k$ be an algebraic function field in one variable, presented through a separating variable: $K$ is a finite separable extension of the rational function field $k(X)$, the structure maps $k\to k[X]\to k(X)\to K$ being compatible. Assume that $k$ is the full constant field of $K$: every element of $K$ that is algebraic over $k$ already lies in $k$.
--
--   A *place* $P$ of $K/k$ is a valuation ring $\mathcal O_P$ with $k\subseteq\mathcal O_P\subsetneq K$ whose value group is infinite cyclic; $v_P:K^\times\to\mathbb Z$ is its normalized valuation and $\deg P=[\mathcal O_P/\mathfrak m_P:k]$ its degree. A *divisor* is a finite formal sum $D=\sum_P n_P\,P$ with $n_P\in\mathbb Z$, of degree $\deg D=\sum_P n_P\deg P$. Its Riemann–Roch space is
--   $$\mathcal L(D)=\{f\in K:\ f=0\ \text{or}\ v_P(f)\ge -n_P\ \text{for every place } P\},$$
--   a $k$-vector space of dimension $\ell(D)$. The *genus* $g$ of $K/k$ is the largest value of the defect $\deg D+1-\ell(D)$ over all divisors $D$.
--
--   An *adele* (répartition) of $K/k$ is a family $a=(a_P)_P$ of elements of $K$, indexed by the places, with $a_P\in\mathcal O_P$ for all but finitely many $P$; the adeles form a $k$-vector space $\mathbb A_K$ containing $K$ diagonally, and for a divisor $D$ one puts $\mathbb A_K(D)=\{a\in\mathbb A_K:\ v_P(a_P)\ge -n_P\ \text{for all } P\}$. A *Weil differential* is a $k$-linear form $\omega:\mathbb A_K\to k$ that vanishes on $\mathbb A_K(D)+K$ for some divisor $D$; if $\omega\neq0$, its divisor $(\omega)$ is the largest divisor $D$ with this property. A divisor $W$ is *canonical* if $W=(\omega)$ for some nonzero Weil differential $\omega$.
--
--   Then $K/k$ admits a canonical divisor:
--   $$\exists\,W\in\operatorname{Div}(K/k)\ \text{and a Weil differential}\ \omega\neq0\ \text{with}\ W=(\omega).$$
--
--   Canonical divisors are the divisors entering the Riemann–Roch theorem $\ell(D)=\deg D+1-g+\ell(W-D)$; this statement guarantees that the theorem and its corollaries are never vacuous.
--
--   **Formalization Note** The tower $k\to k[X]\to k(X)\to K$ is given by the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `Algebra k K`, `IsScalarTower k k[X] K` and `IsScalarTower k[X] k⟮X⟯ K`, together with `FunctionField k K` ($K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`. The full constant field hypothesis is `IsFullConstantField k K`. Places (`FunctionField.Place k K`) are valuation subrings $\mathcal O\neq K$ containing the image of $k$ whose value group admits an order isomorphism with $\mathbb Z^{m0}$ (only its existence is recorded); the normalized valuation is written multiplicatively, $v(f)=e^{-v_P(f)}$, so that $f\in\mathcal L(D)$ reads $v(f)\le e^{n_P}$ for every place. Degrees of places and $\ell(D)$ are `Module.finrank` over $k$, and divisors are finitely supported functions from places to $\mathbb Z$. The genus `FunctionField.genus k K` is defined as the natural-number truncation of the supremum in $\mathbb Z$ of the defects $\deg D+1-\ell(D)$. The adele space is the restricted product of copies of $K$ over the intrinsic places; the divisor of a nonzero Weil differential is defined in the two-chart presentation of places (places over $k[X]$ and places over infinity) and transported to intrinsic places.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.5 (Weil differentials, the divisor of a Weil differential, canonical divisors). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/RiemannRoch.lean#L263-L267

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

theorem FunctionField.exists_isCanonical : ∃ W : Divisor k K, IsCanonical k K W := by sorry
