-- Prove2me | Theorems.Thm_ModularCurve_genusFF_laurentBaseChange_gamma1_mul_add_one_eq_two_mul_genusFF_igusaFunctionFieldX1C_add_natCard
-- name    : ModularCurve.genusFF_laurentBaseChange_gamma1_mul_add_one_eq_two_mul_genusFF_igusaFunctionFieldX1C_add_natCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/ed69d1d2-2cb1-5d49-b927-19f8965fdc20
-- title:
--   Genus identity for X₁(Mp), Igusa curve and supersingular points
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, and let $\Omega$ be an algebraically closed field of characteristic $p$. Let $w$ consist of a modular form of weight $1$ on $\Gamma_1(M)$ together with an integral power series that is its $q$-expansion and whose reduction $\mathrm{intSeriesC}\,\Omega\,w.\mathrm{series}$ in $\Omega((q))$ is non-zero, and let $jbar$ be an element of the intermediate field $\mathrm{x1FunctionFieldC}\,\Omega\,M \subseteq \Omega((q))$, i.e. of the field generated over $\Omega$ by the ratios of integral forms on $\Gamma_1(M)$, whose underlying Laurent series is the reduction $\mathrm{jqModC}\,\Omega = q^{-1}\,(E_4^3\eta^{-24})$ of the $q$-expansion of $j$. Then the genus (the $\overline{\mathbb{Q}}$-dimension of $H^1$ of the zero divisor) of the field obtained from $\mathrm{qExpFunctionFieldC}\,\mathbb{Q}\,(\Gamma_1(Mp))$ by adjoining its coefficientwise image to $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$, plus $1$, equals $2$ times the genus over $\Omega$ of $\mathrm{igusaFunctionFieldX1C}\,\Omega\,M\,w$, the field generated over $\Omega$ by $\mathrm{x1FunctionFieldC}\,\Omega\,M$ together with $(\mathrm{intSeriesC}\,\Omega\,w.\mathrm{series})^{-1}$, plus the number of places $v$ of $\mathrm{x1FunctionFieldC}\,\Omega\,M$ over $\Omega$ at which $jbar$ lies in the valuation subring and the residue value $v.\mathrm{evalAt}\,jbar$ lies in $\mathrm{ssJSet}\,p\,\Omega$, the set of $j \in \Omega$ such that every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $j$ has no non-zero $p$-torsion point.
--
--   This is the dimension identity underlying the semistable reduction of $J_1(Mp)$ at $p$: the special fibre is two copies of the Igusa curve over $X_1(M)_\Omega$ crossing at the supersingular points, so that $g(X_1(Mp)) + 1 = 2g(\mathrm{Ig}) + \#ss$. It upgrades the corresponding inequality to an equality, and is used in the analysis of the torsion and of the toric and abelian ranks of the Jacobian of the model of $X_1(Mp)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_laurentBaseChange_gamma1_mul_add_one_eq_two_mul_genusFF_igusaFunctionFieldX1C_add_natCard.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open ModularCurve
open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.genusFF_laurentBaseChange_gamma1_mul_add_one_eq_two_mul_genusFF_igusaFunctionFieldX1C_add_natCard
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (w : ModularCurve.IntegralWeightOneForm Ω M)
    (jbar : ↥(ModularCurve.x1FunctionFieldC Ω M)) (hjbar : (jbar : LaurentSeries Ω) = ModularCurve.jqModC Ω) :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * p)))) + 1 =
      2 * AlgebraicCurve.genusFF Ω ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) +
        Nat.card {v : AlgebraicCurve.Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M) //
          (jbar : ↥(ModularCurve.x1FunctionFieldC Ω M)) ∈ v.toValuationSubring ∧
            v.evalAt jbar ∈ ModularCurve.ssJSet p Ω} := by sorry
