-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le
-- name    : ModularCurve.FullLevel.adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/c4be1b7c-6fb7-55a2-b655-080fcb82a59f
-- title:
--   Degree of the full-level field over scaled Γ₀(M') functions
-- statement:
--   Let $q$ be a prime with $q \ge 5$, and let $M'$ be a nonzero natural number with $q \nmid M'$. Work inside the Laurent series field $\overline{\mathbb{Q}}((q))$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Write $A$ for the intermediate field generated over $\overline{\mathbb{Q}}$ by the image, under the ring homomorphism `qExpand` that substitutes $q \mapsto q^q$ (embedding the exponent group along multiplication by $q$), of the underlying set of `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))`, i.e. of the field generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the ratios $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ of integral $q$-expansions $p_f,p_g$ of weight-$k$ modular forms $f,g$ for $\Gamma_0(M')$ (with $\mathrm{intSeriesC}(p_g) \neq 0$). Write $\overline{F}$ for `fieldBar q M'`, the field generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `xHFunctionField (q ^ 2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. The assertion is threefold: $A \le \overline{F}$; the relative degree `relfinrank` of $\overline{F}$ over $A$ is strictly positive, hence finite and nonzero; and twice that relative degree is at most $q(q^2-1)$.
--
--   This is the inclusion-plus-degree-bound half of the classical statement that the full-level modular function field of level $q^2M'$ with $H$ the units congruent to $1$ mod $q$ has degree $|\mathrm{PSL}_2(\mathbb{F}_q)| = q(q^2-1)/2$ over the $\Gamma_0(M')$ function field read in $q^q$, i.e. the degree of $X(\Gamma(q) \cap \Gamma_0(M')) \to X_0(M')$. It is used, together with an Artin-type fixed-field argument, in [`ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq`](thm.html#ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq) to identify the elements of the full-level field invariant under the relevant automorphisms as substitutions $g(q^q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ)))) ≤ fieldBar q M' ∧
    0 < (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M') ∧
    2 * (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M') ≤ q * (q ^ 2 - 1) := by sorry
