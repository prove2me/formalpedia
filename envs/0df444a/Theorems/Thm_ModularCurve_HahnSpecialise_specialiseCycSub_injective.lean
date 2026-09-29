-- Prove2me | Theorems.Thm_ModularCurve_HahnSpecialise_specialiseCycSub_injective
-- name    : ModularCurve.HahnSpecialise.specialiseCycSub_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/319e24b6-63cc-58e9-887d-b11e3471b436
-- title:
--   Specialisation is injective on cyclic subgroups of order N
-- statement:
--   Let `H` be the Hahn-series field fixed in this development (its elements carry an order function `orderTop` and coefficients, so that `coeff 0` is defined) and let $\bar{\mathbb Q}$ denote `Qbar`, the algebraic closure of $\mathbb Q$. Let $E$ be a Weierstrass curve over `H` satisfying `IntegralCoeffs`, that is, each of $a_1,a_2,a_3,a_4,a_6$ has nonnegative `orderTop`; let `specialFibre E` be the Weierstrass curve over $\bar{\mathbb Q}$ whose coefficients are the $0$-th coefficients $a_i(0)$, and assume its discriminant $\Delta$ is nonzero. Let $N$ be a natural number with `NeZero N`, i.e. $N \neq 0$. The assertion is that the map `specialiseCycSub E hE hΔ N` is injective. Its source `CycSubH E N` consists of the subgroups $S$ of the affine point group $E(\,$`H`$)$ for which there is a point $g$ of additive order exactly $N$ with $S = \langle g\rangle$ (the group of integer multiples of $g$), its target `CycSub (specialFibre E) N` is the analogous set of subgroups of $(\mathrm{specialFibre}\,E)(\bar{\mathbb Q})$, and the map sends $S$ to its image under the specialisation homomorphism `specialise E hE hΔ` $: E(\,$`H`$) \to (\mathrm{specialFibre}\,E)(\bar{\mathbb Q})$, this image again being cyclic of order $N$ because that homomorphism is injective on pairs of $N$-torsion points.
--
--   This is the injectivity half of the comparison of $\Gamma_0(N)$-level structures — cyclic subgroups of order $N$ — on a Weierstrass curve with good special fibre and on that special fibre, the classical source being the injectivity of reduction on torsion of order prime to the residue characteristic. It feeds the bijectivity statement [`ModularCurve.HahnSpecialise.specialiseCycSub_bijective`](thm.html#ModularCurve.HahnSpecialise.specialiseCycSub_bijective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_HahnSpecialise_specialiseCycSub_injective.lean

import Definitions.Def_ModularCurve_HahnSpecialise

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.B3 ModularCurve.HahnSpecialise
open ModularCurve.TatePoint (Qbar H CycSubH)
open scoped Classical

theorem ModularCurve.HahnSpecialise.specialiseCycSub_injective (E : WeierstrassCurve H) (hE : IntegralCoeffs E)
    (hΔ : (specialFibre E).Δ ≠ 0) (N : ℕ) [NeZero N] :
    Function.Injective (specialiseCycSub E hE hΔ N) := by sorry
