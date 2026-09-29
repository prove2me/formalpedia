-- Prove2me | Theorems.Thm_ModularCurve_mapDomain_heckeDivBar_eq_of_forall_single
-- name    : ModularCurve.mapDomain_heckeDivBar_eq_of_forall_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/9bd29e4c-4afd-5ec2-9420-523a6fbff84c
-- title:
--   Hecke specialisation extends from places to all divisors
-- statement:
--   Let $L$ be a field of characteristic zero (a $\mathbb{Q}$-algebra), and let $N,\ell$ be nonzero natural numbers. Write $F_M =$ `laurentBaseChange L (modularFunctionFieldFull M)` for the subfield of the Laurent series field $L((q))$ generated over $L$ by the coefficientwise images of the field $\mathbb{Q}(\,q\text{-expansions } \mathrm{qExpand}\ \mathbb{Q}\ d\ j_q : d \mid M\,)$. Assume the two level-raising $L$-algebra maps $F_N \to F_{N\ell}$ are integral: `hα` for the inclusion `heckeAlphaBar` coming from the inclusion of function fields, and `hβ` for `heckeBetaBar`, induced by $q \mapsto q^{\ell}$; assume also that $F_{N\ell}$ has principal divisors over $L$, i.e. every nonzero $f$ admits a divisor of degree $0$ whose coefficient at each place $v$ is $v.\mathrm{ord}(f)$. Here a place of $F/K$ is a valuation subring of $F$ containing $K$, proper, and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $\mathrm{heckeDivBar} = \mathrm{(heckeAlphaBar)}_* \circ \mathrm{(heckeBetaBar)}^*$ be the resulting correspondence on divisors of $F_N/L$. Let $F'/k$ be any field extension, let $sp$ be any map from places of $F_N/L$ to places of $F'/k$, and let $E$ be any additive endomorphism of the divisor group of $F'/k$. If for every place $v$ one has $sp_*(\mathrm{heckeDivBar}(v)) = E(sp(v))$ on single-place divisors with coefficient $1$, then for every divisor $D$ of $F_N/L$, $sp_*(\mathrm{heckeDivBar}(D)) = E(sp_* D)$, where $sp_* =$ `Finsupp.mapDomain sp`.
--
--   This is the passage from a per-place identity to a divisor-level identity for the Hecke correspondence on the modular function field of level $N$: the hypothesis is the shape taken by the Eichler–Shimura relation at each place, and the conclusion is the corresponding equality of additive maps on all divisors. It is used when comparing the specialised Hecke divisor with Frobenius-type operators on a special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mapDomain_heckeDivBar_eq_of_forall_single.lean

import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.mapDomain_heckeDivBar_eq_of_forall_single {L : Type*} [Field L] [Algebra ℚ L] {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] {k F' : Type*} [Field k] [Field F'] [Algebra k F'] (sp : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k F') (E : Divisor k F' →+ Divisor k F') (hE : ∀ v : Place L (laurentBaseChange L (modularFunctionFieldFull N)), Finsupp.mapDomain sp (heckeDivBar hα hβ (Finsupp.single v 1)) = E (Finsupp.single (sp v) 1)) (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :
    Finsupp.mapDomain sp (heckeDivBar hα hβ D) = E (Finsupp.mapDomain sp D) := by sorry
