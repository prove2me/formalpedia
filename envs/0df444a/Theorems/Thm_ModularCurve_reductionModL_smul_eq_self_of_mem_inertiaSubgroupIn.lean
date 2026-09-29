-- Prove2me | Theorems.Thm_ModularCurve_reductionModL_smul_eq_self_of_mem_inertiaSubgroupIn
-- name    : ModularCurve.reductionModL_smul_eq_self_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/6e43437f-76f3-5b39-9b70-ede4d80ad990
-- title:
--   Inertia acts trivially after reduction of Pic⁰
-- statement:
--   Let $N$ be a nonzero natural number and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Assume [`ModularCurve.ReductionInputsModL A N`](def/ModularCurve_ReductionModL.html#L184), i.e. `ReductionInputsAlong` holds for $A$ along the residue map $A \to$ `IsLocalRing.ResidueField A` at level $N$: there exists a map $r$ on the places of the base-changed full modular function field which is a place reduction along this data (`IsPlaceReductionAlong`) and which satisfies `PrincipalGeneratedByIntegral`. Let $\tau$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ belonging to `A.inertiaSubgroupIn ℚ`, the image in the full automorphism group of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $A$. Let $z$ be an element of [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), that is of $\mathrm{Pic}^0$ of the field `modularFunctionFieldBar N` (the base change to $\overline{\mathbb{Q}}$, inside Laurent series, of `modularFunctionFieldFull N`) over $\overline{\mathbb{Q}}$, formed as degree-zero divisors modulo principal ones. Then the reduction homomorphism [`ModularCurve.reductionModL A N`](def/ModularCurve_ReductionModL.html#L199), with values in $\mathrm{Pic}^0$ over the residue field of $A$, takes the same value at $\tau \cdot z$, for the arithmetic Galois action on `JZero N`, as at $z$.
--
--   This is the statement that the inertia group of $A$ acts trivially on the reduction of the degree-zero divisor class group of the modular curve of level $N$, the function-field form of the classical fact that inertia acts trivially on the reduction of an abelian variety with good reduction. It is used in the analysis of the inertia action on the Tate module of $J_0(N)$, for instance in deducing that Frobenius satisfies its quadratic relation on eigenplanes and in the results on Eisenstein torsion and on inertia orbits in `JZero N`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_reductionModL_smul_eq_self_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.reductionModL_smul_eq_self_of_mem_inertiaSubgroupIn (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (h : ModularCurve.ReductionInputsModL A N)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (z : ModularCurve.JZero N) :
    ModularCurve.reductionModL A N (τ • z) = ModularCurve.reductionModL A N z := by sorry
