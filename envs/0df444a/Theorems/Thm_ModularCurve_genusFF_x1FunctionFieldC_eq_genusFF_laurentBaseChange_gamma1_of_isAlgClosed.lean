-- Prove2me | Theorems.Thm_ModularCurve_genusFF_x1FunctionFieldC_eq_genusFF_laurentBaseChange_gamma1_of_isAlgClosed
-- name    : ModularCurve.genusFF_x1FunctionFieldC_eq_genusFF_laurentBaseChange_gamma1_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/9f113a62-e005-5caa-898b-4b5e24c0d232
-- title:
--   Genus of X₁(M) unchanged in characteristic p ∤ M
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, and let $\kappa$ be an algebraically closed field of characteristic $p$. The assertion is an equality of two genera, each computed as [`AlgebraicCurve.genusFF`](def/AlgebraicCurve_Repartitions.html#L145), i.e. as the dimension over the coefficient field of $H^1$ of the zero divisor of the relevant function field. On the left stands the genus over $\kappa$ of [`ModularCurve.x1FunctionFieldC κ M`](def/ModularCurve_X1.html#L134), which by definition is [`ModularCurve.qExpFunctionFieldC κ (CongruenceSubgroup.Gamma1 M)`](def/ModularCurve_X1.html#L101): the subfield of the Laurent series field $\kappa((q))$ generated over $\kappa$ by all quotients $\mathrm{intSeriesC}\,\kappa\,p_f / \mathrm{intSeriesC}\,\kappa\,p_g$, where $f,g$ run over modular forms of some weight $k$ for $\Gamma_1(M)$ (viewed inside $\mathrm{GL}_2(\mathbb{R})$) admitting integral $q$-expansions $p_f,p_g \in \mathbb{Z}[[q]]$ and the reduction of $p_g$ is nonzero. On the right stands the genus over $\overline{\mathbb{Q}}$ (the field `AlgebraicClosure ℚ`) of [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), namely the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the corresponding field [`ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)`](def/ModularCurve_X1.html#L101) $\subseteq \mathbb{Q}((q))$ under the map applying $\mathbb{Q} \to \overline{\mathbb{Q}}$ to each Laurent coefficient. The two genera are equal.
--
--   This is the Igusa-type statement that the genus of the modular curve $X_1(M)$ is unchanged under reduction to characteristic $p$ when $p \nmid M$, here in the $q$-expansion function field formulation and for an arbitrary algebraically closed coefficient field of characteristic $p$. It feeds the comparison of the genus of $X_1(M)$ with that of the Igusa curve and the degree/genus count for the relevant double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_x1FunctionFieldC_eq_genusFF_laurentBaseChange_gamma1_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.genusFF_x1FunctionFieldC_eq_genusFF_laurentBaseChange_gamma1_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] :
    AlgebraicCurve.genusFF κ ↥(ModularCurve.x1FunctionFieldC κ M) =
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) := by sorry
