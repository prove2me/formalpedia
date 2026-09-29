-- Prove2me | Theorems.Thm_ModularCurve_pic0_x1x0FunctionFieldC_smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn
-- name    : ModularCurve.pic0_x1x0FunctionFieldC_smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/d7c53893-86f1-5417-af39-1650cd2eeafa
-- title:
--   Inertia at q is unipotent of echelon two
-- statement:
--   Let $M_0$ be a nonzero natural number and $q$ a prime not dividing $M_0$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense that the image of $q$ lies in the nonunits of $P$, and let $\sigma,\tau$ be $\mathbb{Q}$-automorphisms of $\overline{\mathbb{Q}}$ belonging to `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup of $P$. Let $F_0 =$ [`ModularCurve.x1x0FunctionFieldC ℚ M₀ q`](def/ModularCurve_X1.html#L142) be the subfield of $\mathbb{Q}((X))$ generated over $\mathbb{Q}$ by the ratios of integral forms `intFormRatiosC` for the group $\Gamma_1(M_0) \cap \Gamma_0(q)$, and let $F$ be its Laurent base change, the subfield of $\overline{\mathbb{Q}}((X))$ generated over $\overline{\mathbb{Q}}$ by the image of $F_0$ under the coefficientwise extension of $\mathbb{Q} \to \overline{\mathbb{Q}}$. Let $z$ be an element of $\mathrm{Pic}^0$ of $F/\overline{\mathbb{Q}}$, that is, of the group of finitely supported $\mathbb{Z}$-valued divisors on the places of $F/\overline{\mathbb{Q}}$ of degree zero modulo the principal ones, and suppose $n \cdot z = 0$ for some natural number $n$ not divisible by $q$. Then, for the Galois action on $\mathrm{Pic}^0$, $\tau \cdot (\sigma \cdot z - z) = \sigma \cdot z - z$.
--
--   This is the Grothendieck monodromy statement for the Jacobian of the modular curve of level $\Gamma_1(M_0) \cap \Gamma_0(q)$ with $q \nmid M_0$: on torsion of order prime to $q$, the operator $(\tau - 1)(\sigma - 1)$ vanishes for $\sigma,\tau$ in the inertia group at a place above $q$, which is the group-theoretic form of semistable reduction at $q$ in the sense of Deligne–Rapoport. It feeds the analysis of the action of inertia at $q$ on $J_1$ used in the level-lowering step, being cited by [`ModularCurve.JOne.smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn_of_eq_sum_diamondOneBar`](thm.html#ModularCurve.JOne.smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn_of_eq_sum_diamondOneBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pic0_x1x0FunctionFieldC_smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.pic0_x1x0FunctionFieldC_smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn
    (M₀ q : ℕ) [NeZero M₀] (hq : q.Prime) (hqM₀ : ¬ q ∣ M₀)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (z : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ q)))
    (n : ℕ) (hn : ¬ q ∣ n) (hz : (n : ℤ) • z = 0) :
    τ • (σ • z - z) = σ • z - z := by sorry
