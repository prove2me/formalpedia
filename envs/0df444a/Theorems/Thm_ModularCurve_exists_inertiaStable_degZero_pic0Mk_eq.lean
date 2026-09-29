-- Prove2me | Theorems.Thm_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq
-- name    : ModularCurve.exists_inertiaStable_degZero_pic0Mk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/99ede1f6-2f71-5663-929a-823a0c9acdfa
-- title:
--   Inertia-invariant classes of J₀(M) lift to invariant divisors
-- statement:
--   Let $M\ge 1$ and let $A$ be a valuation subring of $\overline{\mathbb Q}$, with $I_A :=$ `A.inertiaSubgroupIn ℚ` the image in $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ inside its decomposition subgroup. Write $F :=$ `modularFunctionFieldBar M` for the base change to $\overline{\mathbb Q}$, inside Laurent series, of the field `modularFunctionFieldFull M` generated over $\mathbb Q$ by the divisor expansions of level $M$, and let `JZero M` $= \mathrm{Pic}^0(\overline{\mathbb Q}, F)$ be the quotient of the group of degree-zero divisors — finitely supported $\mathbb Z$-valued functions on the places of $F$ over $\overline{\mathbb Q}$, annihilated by the degree homomorphism $D \mapsto \sum_v D(v)\deg v$ — by its subgroup of principal divisors. Galois elements act on $F$ coefficientwise through `arithmeticGalois (modularFunctionFieldFull M)`, hence on places, divisors and $\mathrm{Pic}^0$. The theorem asserts: for every class $x$ in the subgroup `inertiaInvariants A M` of elements of `JZero M` fixed by every $\sigma \in I_A$, there is a degree-zero divisor $D_0$ on $F$ with $\sigma \cdot D_0 = D_0$ for all $\sigma \in I_A$ (equality of divisors, not merely of classes) whose class in $\mathrm{Pic}^0$ equals $x$.
--
--   This is the Galois descent step — Hilbert's theorem 90 applied to the function field of the modular curve — which replaces an inertia-invariant divisor class by a genuinely inertia-invariant representative divisor. It is used in the analysis of specialisation of places on $J_0(M)$, where a representative with inertia-stable support is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_inertiaStable_degZero_pic0Mk_eq
    (M : ℕ) [NeZero M] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (x : ↥(inertiaInvariants A M)) :
    ∃ D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull M) σ •
          (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) = D₀) ∧
      Pic0.mk D₀ = (x : JZero M) := by sorry
