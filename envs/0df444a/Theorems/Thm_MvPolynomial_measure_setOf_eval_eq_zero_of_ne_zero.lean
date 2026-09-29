-- Prove2me | Theorems.Thm_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero
-- name    : MvPolynomial.measure_setOf_eval_eq_zero_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/c88f2221-9900-5055-bb16-3cf1e95020e0
-- title:
--   Zero sets of non-zero polynomials are Haar-null
-- statement:
--   Let $F$ be a field carrying a topology making it a topological ring, which is locally compact, Hausdorff and second countable, equipped with its Borel $\sigma$-algebra, and assume $F$ is not discrete. Let $\iota$ be a finite index set, let $p \in F[X_k : k \in \iota]$ be a multivariate polynomial with $p \neq 0$, and let $\mu$ be a measure on the product space $\iota \to F$ that is an additive Haar measure (left-invariant, finite and positive on compacts, in Mathlib's sense `IsAddHaarMeasure`). The conclusion is that the set of $x : \iota \to F$ at which $p$ evaluates to $0$, i.e. the affine hypersurface $\{x \mid p(x) = 0\} \subseteq F^{\iota}$, has $\mu$-measure zero. Note that no irreducibility or degree hypothesis is imposed on $p$, and the measure $\mu$ is an arbitrary additive Haar measure on $F^{\iota}$ rather than a specified product measure.
--
--   This is the standard statement that a proper algebraic subvariety of affine space over a non-discrete locally compact field is null for Haar measure; for $F = \mathbb{R}$, $\mathbb{C}$ or a local field it is the basic genericity fact underlying integration over hypersurfaces. It is used in the adelic measure-theoretic estimates for automorphic forms, where non-vanishing of a determinant or a norm has to be arranged for almost all points of an adelic box.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MvPolynomial.measure_setOf_eval_eq_zero_of_ne_zero
    (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F] [T2Space F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (hF : ¬ DiscreteTopology F)
    (ι : Type) [Fintype ι] (p : MvPolynomial ι F) (hp : p ≠ 0)
    (μ : Measure (ι → F)) [μ.IsAddHaarMeasure] :
    μ {x : ι → F | MvPolynomial.eval x p = 0} = 0 := by sorry
