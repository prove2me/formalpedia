-- Prove2me | Theorems.Thm_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH
-- name    : ModularCurve.exists_inertiaStable_degZero_pic0Mk_eq_xH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/eef4d020-a6a7-59d4-9295-cbfc6980f86b
-- title:
--   Inertia-stable divisor representing an inertia-fixed class of J_H
-- statement:
--   Fix $M \ge 1$ (a natural number assumed nonzero) and a subgroup $H \le (\mathbb{Z}/M)^\times$, and let $F =$ `xHFunctionFieldBar M H` be the intermediate field of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the $q$-expansion function field `xHFunctionField M H` of level $\Gamma_H(M)$; here $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`. Divisors are the finitely supported $\mathbb{Z}$-valued functions on the places of $F$ over $\overline{\mathbb{Q}}$ (valuation subrings of $F$ containing $\overline{\mathbb{Q}}$, proper in $F$, and principal ideal rings), the degree-zero subgroup is the kernel of $D \mapsto \sum_v D(v)\deg v$, and $J_H(M) =$ `JH M H` is the quotient of the degree-zero divisors by the principal ones. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, and let $I_A \le \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be the image in the full automorphism group of the inertia subgroup of $A$ over $\mathbb{Q}$ (that is, `A.inertiaSubgroupIn ℚ`). Let $x \in J_H(M)$ satisfy $\sigma \bullet x = x$ for all $\sigma \in I_A$. Then there is a degree-zero divisor $D_0$ on $F$ such that $D_0$ is fixed by the semilinear automorphism `arithmeticGalois (xHFunctionField M H) σ` attached to each $\sigma \in I_A$ (the coefficientwise action of $\sigma$ on Laurent series, acting on divisors through places), and the class of $D_0$ in $J_H(M)$ is $x$.
--
--   This is the Galois descent step saying that an inertia-invariant point of the Jacobian of $X_H(M)$ over $\overline{\mathbb{Q}}$ is represented by a divisor that is itself stable under the inertia group, so that the class may be studied through an explicit divisor when specialising at places. It is used in the analysis of inertia-invariant classes via place specialisation, where a representative with controlled support is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_inertiaStable_degZero_pic0Mk_eq_xH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (x : JH M H) (hx : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) :
    ∃ D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (xHFunctionField M H) σ •
          (D₀ : Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)) = D₀) ∧
      Pic0.mk D₀ = x := by sorry
