-- Prove2me | Theorems.Thm_LaurentSeries_exists_eq_C_of_isAlgebraic
-- name    : LaurentSeries.exists_eq_C_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/de7f6350-8900-5443-9157-b8667a4ff1a4
-- title:
--   A field is algebraically closed in its Laurent series field
-- statement:
--   Let $K$ be a field (in an arbitrary universe) and let $x$ be an element of `LaurentSeries K`, i.e. a Hahn series over the value group $\mathbb{Z}$ with coefficients in $K$. Assume `IsAlgebraic K x`, that is, there is a nonzero polynomial in $K[X]$ whose evaluation at $x$, along the structure map of $K$ into `LaurentSeries K`, is zero. The conclusion is that there exists a scalar $c \in K$ with $x =$ `HahnSeries.C c`, the Hahn series whose only possibly nonzero coefficient is the one in degree $0$, equal to $c$. In other words, every Laurent series over $K$ that is algebraic over $K$ is a constant series, so that $K$ is relatively algebraically closed in $K((q))$; the constant produced is necessarily the coefficient of $x$ in degree $0$. No restriction is placed on the characteristic of $K$, nor is $K$ assumed perfect or the polynomial assumed irreducible or separable.
--
--   This is the statement that the constant field of the Laurent series field $K((q))$ is $K$ itself. It is used in the treatment of function fields of modular curves, for instance to identify the elements of the $q$-expansion function field, and of the full modular function field, that are algebraic over the base field, and in a bound on the cardinality of an inertia group for a model of $X_0(p)$-type curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_exists_eq_C_of_isAlgebraic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem LaurentSeries.exists_eq_C_of_isAlgebraic
    {K : Type u} [Field K] (x : LaurentSeries K) (hx : IsAlgebraic K x) :
    ∃ c : K, x = HahnSeries.C c := by sorry
