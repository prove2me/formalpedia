-- Prove2me | Theorems.Thm_FunctionField_Chart_placeValuation_algebraMap_eq_one
-- name    : FunctionField.Chart.placeValuation_algebraMap_eq_one
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T13:37:41.400985+00:00
-- url     : https://prove2.me/theorems/19e5ea41-44e0-41e0-8b86-8883f59b3ec2
-- title:
--   Nonzero constants have valuation one at every coordinate place of a function field
-- statement:
--   Let $k$ be a field and let $K$ be a finite separable extension of the rational function field $k(X)$, with compatible structure maps $k\to k[X]\to k(X)\to K$ (no assumption is made on the constant field). Let $\mathcal O_K$ be the integral closure of $k[X]$ in $K$, and let $\mathcal O_{K,\infty}$ be the integral closure in $K$ of the valuation ring at infinity
--   $$\mathcal O_\infty=\{f\in k(X):\ \deg f\le 0\},\qquad \deg f=\deg(\text{numerator})-\deg(\text{denominator}).$$
--   Both are Dedekind domains with fraction field $K$. A *coordinate place* of $K$ is a nonzero prime $\mathfrak p$ of $\mathcal O_K$ (a finite place) or of $\mathcal O_{K,\infty}$ (a place at infinity); its $\mathfrak p$-adic valuation is written multiplicatively, $v_{\mathfrak p}(f)=e^{-\operatorname{ord}_{\mathfrak p}(f)}$ for $f\in K^\times$, with values in $\{0\}\cup e^{\mathbb Z}$.
--
--   Then for every coordinate place $\mathfrak p$ and every nonzero constant $c\in k^\times$,
--   $$v_{\mathfrak p}(c)=1,\qquad\text{i.e.}\qquad \operatorname{ord}_{\mathfrak p}(c)=0.$$
--
--   Thus constants are units at every finite and infinite place of the two-chart presentation; for instance, multiplying a function by a nonzero constant does not change its principal divisor.
--
--   **Formalization Note** The coordinate places are `PlaceA k K`, the sum of the height-one spectra of `ringOfIntegers k K` and of `infiniteIntegers k K`, and `placeValuation k K v` is Mathlib's adic valuation `HeightOneSpectrum.valuation K` with values in $\mathbb Z^{m0}$. The tower is given by `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, `FunctionField k K` (finite-dimensionality over $k(X)$), `Algebra.IsSeparable k⟮X⟯ K`, and the constants by `Algebra k K` with `IsScalarTower k k[X] K`. A classical decidable-equality instance on $k(X)$, used to define the valuation at infinity, is activated locally; it carries no mathematical content.
-- source:
--   Auxiliary lemma of the formalization: the coordinate-chart form of the fact that a nonzero constant is a unit in the valuation ring of every place (cf. H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.1). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/Place.lean#L594-L605

import Mathlib
import Definitions.Def_RiemannRoch_Places
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
variable (k K : Type*) [Field k] [Field K]
open MonoidWithZeroHom
open FunctionField.Chart
attribute [local instance] FunctionField.Chart.instDecidableEqRatFuncRiemannRoch
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
variable [Algebra k K] [IsScalarTower k k[X] K]

theorem FunctionField.Chart.placeValuation_algebraMap_eq_one (v : PlaceA k K) (c : kˣ) :
    placeValuation k K v (algebraMap k K (c : k)) = 1 := by sorry
