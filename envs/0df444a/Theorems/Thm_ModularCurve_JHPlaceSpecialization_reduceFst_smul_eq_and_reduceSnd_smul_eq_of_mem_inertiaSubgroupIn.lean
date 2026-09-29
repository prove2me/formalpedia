-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
-- name    : ModularCurve.JHPlaceSpecialization.reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/96e8e0a8-9c9a-5889-80ce-8c2fb2720d1b
-- title:
--   Inertia-invariance of the two place readings on X_H(M)
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$, a subgroup $H \le (\mathbb Z/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M$ for $\overline{\mathbb Q}\cdot F(\Gamma_H(M))$, the base change to $\overline{\mathbb Q}$ of the intermediate field `xHFunctionField M H` inside Laurent series over $\mathbb Q$, and $F_{M/p}$ for the corresponding field at level $M/p$ with group `infSubgroup p M H hpM`, the image of $H$ under the reduction of units. Given: a $\overline{\mathbb Q}$-algebra automorphism $\theta$ of $F_M$; two integral $\overline{\mathbb Q}$-algebra maps $\alpha,\beta : F_{M/p}\to F_M$; an arbitrary self-map $\delta$ of the set of places of $\kappa \cdot F_b$, where $F_b$ is `JHNeronObjectAtP.Fbar p M H hpM κ`; and a term `Psp` of the structure `JHPlaceSpecialization p M H hpM A`, whose data include a map $\mathrm{sp}$ from places of $F_{M/p}$ over $\overline{\mathbb Q}$ to places of $F_b$ over $\kappa$ satisfying, among other clauses, inertia-invariance (`d6_inertia`). Assume $\alpha$ leaves the underlying Laurent series of every element unchanged, $\theta$ commutes with the arithmetic Galois action `arithmeticGalois` of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$, and $\beta = \theta\circ\alpha$. Then for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb Q$ (the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup inside the decomposition subgroup) and every place $V$ of $F_M$ over $\overline{\mathbb Q}$, both readings are unchanged by $\sigma$: $\mathrm{sp}(V^{\sigma}|_{\alpha}) = \mathrm{sp}(V|_{\alpha})$ and $\delta(\mathrm{sp}(V^{\sigma}|_{\beta})) = \delta(\mathrm{sp}(V|_{\beta}))$, where $V^{\sigma}$ denotes the translate of $V$ by $\sigma$ through `arithmeticGalois` and $V|_{\alpha}$, $V|_{\beta}$ the restrictions of $V$ along $\alpha$, $\beta$.
--
--   This is the inertia-equivariance of the two degeneracy readings (reduction along $\alpha$ and along $\beta = \theta\circ\alpha$) attached to a place-specialization datum for $X_H(M)$ at a prime $p$ exactly dividing the level, the setting in which the fibre at $p$ is a union of two copies of $X_{H'}(M/p)$. It is used in the statements about inertia-stable divisor classes and principal degree-zero divisors supported in inertia orbits that enter the level-lowering argument at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceFst α hα (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V) = Psp.reduceFst α hα V ∧
    Psp.reduceSnd β hβ δ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V) = Psp.reduceSnd β hβ δ V := by sorry
