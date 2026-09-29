-- Prove2me | Theorems.Thm_ModularCurve_exists_place_of_ringHom_laurentSeries
-- name    : ModularCurve.exists_place_of_ringHom_laurentSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/021fe713-cbe4-5365-977e-04494dec25f2
-- title:
--   A Laurent expansion with a uniformiser defines a place
-- statement:
--   Let $k$, $F$, $K$ be fields with $F$ and $K$ both $k$-algebras, and let $\theta\colon F \to K((X))$ be a ring homomorphism into the field of formal Laurent series over $K$ such that $\theta(a) = a$ for constants, i.e. $\theta(\mathrm{algebraMap}_{k,F}(a))$ is the constant series with value $\mathrm{algebraMap}_{k,K}(a)$ for every $a \in k$, and assume that some $x \in F$ has $\theta(x)$ of order exactly $1$. Then there is a place $v$ of $F$ over $k$ in the sense of the project, that is, a valuation subring $\mathcal{O} = v.\mathrm{toValuationSubring}$ of $F$ which contains the image of $k$, is not all of $F$, and is a principal ideal ring, such that: (i) for every $f \in F$, $f \in \mathcal{O}$ if and only if the order of $\theta(f)$ is $\ge 0$; (ii) for every $f \in F$, the invariant $v.\mathrm{ord}\,f$, defined as minus the $\mathrm{WithZero}$-logarithm of the value of $f$ under the adic valuation attached to the height-one prime of $\mathcal{O}$, equals the order of $\theta(f)$; and (iii) there is a $k$-algebra homomorphism $\iota$ from the residue field of $\mathcal{O}$ to $K$ with $\iota$ of the residue class of $x \in \mathcal{O}$ equal to the coefficient of $X^0$ in $\theta(x)$. The three conclusions are bundled into a single existence statement because $\iota$ is defined on the residue field of the place produced.
--
--   This is the pullback of the $X$-adic (i.e. $q$-adic) valuation of $K((X))$ along a Laurent-series expansion: a $q$-expansion map with a uniformiser in its image cuts out a place of the function field, with $\mathrm{ord}$ read off from the order of the expansion and the constant term inducing an embedding of the residue field into $K$. It is used in the cusp-expansion analysis of modular curves, by [`ModularCurve.PlaceSpecialization.exists_sum_ord_isInftySide_eq_order_sub_order`](thm.html#ModularCurve.PlaceSpecialization.exists_sum_ord_isInftySide_eq_order_sub_order) and by [`ModularCurve.finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq`](thm.html#ModularCurve.finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_place_of_ringHom_laurentSeries.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.exists_place_of_ringHom_laurentSeries
    {k F K : Type*} [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    (θ : F →+* LaurentSeries K)
    (hθ : ∀ a : k, θ (algebraMap k F a) = HahnSeries.C (algebraMap k K a))
    (hunif : ∃ x : F, (θ x).order = 1) :
    ∃ v : AlgebraicCurve.Place k F,
      (∀ f : F, f ∈ v.toValuationSubring ↔ 0 ≤ (θ f).order) ∧
      (∀ f : F, v.ord f = (θ f).order) ∧
      ∃ ι : v.ResidueField →ₐ[k] K,
        ∀ x : v.toValuationSubring, ι (IsLocalRing.residue v.toValuationSubring x) = (θ (x : F)).coeff 0 := by sorry
