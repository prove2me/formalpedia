-- Prove2me | Theorems.Thm_ModularCurve_HahnSpecialise_specialise_bijOn_torsion
-- name    : ModularCurve.HahnSpecialise.specialise_bijOn_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/efd9b02b-cf7a-51ab-8940-ed4ca3c344a2
-- title:
--   Specialisation is bijective on N-torsion
-- statement:
--   Let $H$ be the field of Hahn series with rational exponents over an algebraic closure $\bar{\mathbb Q}$ of $\mathbb Q$, and let $E$ be a Weierstrass curve over $H$. Assume `IntegralCoeffs E`, i.e. each of the five coefficients $a_1,a_2,a_3,a_4,a_6$ of $E$ has $\mathrm{orderTop}\ge 0$, so that all of them lie in the valuation subring `valuationSubringH` of Hahn series with non-negative support. Let `specialFibre E` be the Weierstrass curve over $\bar{\mathbb Q}$ whose coefficients are the degree-$0$ Hahn coefficients of the $a_i$, and assume its discriminant $\Delta$ is non-zero. Let $N$ be a natural number, non-zero. Then the additive group homomorphism `specialise E hE hΔ` from the affine point group $E(H)$ to that of `specialFibre E` over $\bar{\mathbb Q}$ — obtained by viewing $E$ as the base change of the model `liftModel E hE` over `valuationSubringH`, reducing points by `reduceHom`, and transporting along the identification of the residue field with $\bar{\mathbb Q}$ — maps the set $\{P : N\cdot P = 0\}$ bijectively onto $\{Q : N\cdot Q = 0\}$: it sends the first set into the second, is injective on it, and is onto it.
--
--   This is the statement that reduction from the Hahn-series field to its residue field $\bar{\mathbb Q}$ is an isomorphism on $N$-torsion for a model with non-degenerate special fibre (residue characteristic $0$, so no condition on $N$ is needed). It is used to transport $N$-torsion and cyclic level structures between a curve over $H$ and its special fibre, being cited by [`ModularCurve.HahnSpecialise.specialiseCycSub_bijective`](thm.html#ModularCurve.HahnSpecialise.specialiseCycSub_bijective) and [`ModularCurve.B3.exists_torsionBy_reduction_addEquiv`](thm.html#ModularCurve.B3.exists_torsionBy_reduction_addEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_HahnSpecialise_specialise_bijOn_torsion.lean

import Definitions.Def_ModularCurve_HahnSpecialise

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.B3 ModularCurve.HahnSpecialise
open ModularCurve.TatePoint (Qbar H CycSubH)
open scoped Classical

theorem ModularCurve.HahnSpecialise.specialise_bijOn_torsion (E : WeierstrassCurve H) (hE : IntegralCoeffs E)
    (hΔ : (specialFibre E).Δ ≠ 0) (N : ℕ) [NeZero N] :
    Set.BijOn (specialise E hE hΔ) {P | N • P = 0} {Q | N • Q = 0} := by sorry
