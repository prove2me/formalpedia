-- Prove2me | Theorems.Thm_LaurentSeries_exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one
-- name    : LaurentSeries.exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/00b956f6-0bdc-5e8e-b58e-b13eee12845d
-- title:
--   Roots of unity in subfields of k₀((X)) are constants in A₀
-- statement:
--   Let $k_0$ be a field and let $K$ be an intermediate field of the extension $k_0 \subseteq \mathrm{LaurentSeries}\ k_0 = k_0((X))$, i.e. a subfield of the field of formal Laurent series over $k_0$ containing the constants. Let $A_0$ be a valuation subring of $k_0$, and suppose $K$ carries an $A_0$-algebra structure compatible, as a scalar tower, with the inclusions $A_0 \subseteq k_0 \subseteq K$. Let $n$ be a natural number with $n \neq 0$, and let $\zeta \in K$ satisfy $\zeta^n = 1$. The assertion is that there exists $a \in A_0$ with $a^n = 1$ and $\mathrm{algebraMap}\ A_0\ K\ a = \zeta$; that is, every $n$-th root of unity of $K$ is the image of an $n$-th root of unity of the valuation ring $A_0$, hence in particular is a constant Laurent series with coefficient in $A_0$.
--
--   This is the combination of two standard facts: a field is algebraically closed inside its field of formal Laurent series, so the torsion of $K^\times$ consists of constants; and a valuation ring of a field contains all roots of unity of that field. It is used in the construction of level structures on modular curves over Laurent series bases, where Weil pairing values are roots of unity and must be recognised as constants defined over the valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LaurentSeries.exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one
    {k₀ : Type*} [Field k₀] (K : IntermediateField k₀ (LaurentSeries k₀))
    (A₀ : ValuationSubring k₀) [Algebra A₀ K] [IsScalarTower A₀ k₀ K]
    {n : ℕ} (hn : n ≠ 0) (ζ : K) (hζ : ζ ^ n = 1) :
    ∃ a : A₀, a ^ n = 1 ∧ algebraMap A₀ K a = ζ := by sorry
