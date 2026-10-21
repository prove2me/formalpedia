-- Prove2me | Theorems.Thm_FunctionField_ell_eq_of_deg_ge
-- name    : FunctionField.ell_eq_of_deg_ge
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T14:08:50.956761+00:00
-- url     : https://prove2.me/theorems/3c64e20e-5d1f-468e-961c-630cd3700725
-- title:
--   Divisors of degree at least $2g-1$ are non-special: $\ell(D)=\deg D+1-g$
-- statement:
--   Let $k$ be a field and let $K/k$ be an algebraic function field in one variable, presented through a separating variable: $K$ is a finite separable extension of the rational function field $k(X)$, the structure maps $k\to k[X]\to k(X)\to K$ being compatible. Assume that $k$ is the full constant field of $K$: every element of $K$ that is algebraic over $k$ already lies in $k$.
--
--   A *place* $P$ of $K/k$ is a valuation ring $\mathcal O_P$ with $k\subseteq\mathcal O_P\subsetneq K$ whose value group is infinite cyclic; $v_P:K^\times\to\mathbb Z$ is its normalized valuation and $\deg P=[\mathcal O_P/\mathfrak m_P:k]$ its degree. A *divisor* is a finite formal sum $D=\sum_P n_P\,P$ with $n_P\in\mathbb Z$, of degree $\deg D=\sum_P n_P\deg P$. Its Riemann–Roch space is
--   $$\mathcal L(D)=\{f\in K:\ f=0\ \text{or}\ v_P(f)\ge -n_P\ \text{for every place } P\},$$
--   a $k$-vector space of dimension $\ell(D)$. The *genus* $g$ of $K/k$ is the largest value of the defect $\deg D+1-\ell(D)$ over all divisors $D$.
--
--   An *adele* (répartition) of $K/k$ is a family $a=(a_P)_P$ of elements of $K$, indexed by the places, with $a_P\in\mathcal O_P$ for all but finitely many $P$; the adeles form a $k$-vector space $\mathbb A_K$ containing $K$ diagonally, and for a divisor $D$ one puts $\mathbb A_K(D)=\{a\in\mathbb A_K:\ v_P(a_P)\ge -n_P\ \text{for all } P\}$. A *Weil differential* is a $k$-linear form $\omega:\mathbb A_K\to k$ that vanishes on $\mathbb A_K(D)+K$ for some divisor $D$; if $\omega\neq0$, its divisor $(\omega)$ is the largest divisor $D$ with this property. A divisor $W$ is *canonical* if $W=(\omega)$ for some nonzero Weil differential $\omega$.
--
--   Assume that $W$ is a canonical divisor of $K/k$ (this hypothesis is part of the statement; such a $W$ always exists). Let $D$ be a divisor with
--   $$\deg D\ \ge\ 2g-1 .$$
--   Then
--   $$\ell(D)=\deg D+1-g .$$
--
--   This is the "second part" of the Riemann–Roch theorem: for divisors of large degree the dimension of $\mathcal L(D)$ is determined by the degree and the genus alone. It is the form used in practice to compute Riemann–Roch spaces, e.g. $\ell(nO)=n$ for $n\ge1$ on an elliptic curve.
--
--   **Formalization Note** The tower $k\to k[X]\to k(X)\to K$ is given by the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `Algebra k K`, `IsScalarTower k k[X] K` and `IsScalarTower k[X] k⟮X⟯ K`, together with `FunctionField k K` ($K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`. The full constant field hypothesis is `IsFullConstantField k K`. Places (`FunctionField.Place k K`) are valuation subrings $\mathcal O\neq K$ containing the image of $k$ whose value group admits an order isomorphism with $\mathbb Z^{m0}$ (only its existence is recorded); the normalized valuation is written multiplicatively, $v(f)=e^{-v_P(f)}$, so that $f\in\mathcal L(D)$ reads $v(f)\le e^{n_P}$ for every place. Degrees of places and $\ell(D)$ are `Module.finrank` over $k$, and divisors are finitely supported functions from places to $\mathbb Z$. The genus `FunctionField.genus k K` is defined as the natural-number truncation of the supremum in $\mathbb Z$ of the defects $\deg D+1-\ell(D)$. The adele space is the restricted product of copies of $K$ over the intrinsic places; the divisor of a nonzero Weil differential is defined in the two-chart presentation of places (places over $k[X]$ and places over infinity) and transported to intrinsic places. The canonical divisor `W` and the hypothesis `hW : IsCanonical k K W` are arguments of the theorem although `W` does not occur in the conclusion. Degrees and dimensions are compared in $\mathbb Z$.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Theorem 1.5.17 (Riemann–Roch, part two: $\deg A\ge 2g-1$ implies $\ell(A)=\deg A+1-g$). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/RiemannRoch.lean#L306-L314

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
variable {W : Divisor k K} (hW : IsCanonical k K W)
include hW

theorem FunctionField.ell_eq_of_deg_ge (D : Divisor k K)
    (hdeg : D.deg ≥ 2 * (genus k K : ℤ) - 1) :
    (ell k K D : ℤ) = D.deg + 1 - (genus k K : ℤ) := by sorry
