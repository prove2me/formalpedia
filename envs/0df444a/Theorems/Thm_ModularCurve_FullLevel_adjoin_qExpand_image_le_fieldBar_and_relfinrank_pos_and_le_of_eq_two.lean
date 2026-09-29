-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_two
-- name    : ModularCurve.FullLevel.adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/36a37413-aa9a-52b1-9b4e-309d2f63845e
-- title:
--   Full-level field over q-scaled Γ₀(M') field: q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, and let $M'$ be a nonzero natural number not divisible by $q$. Work inside the Laurent series field $\overline{\mathbb{Q}}(\!(X)\!)$ over an algebraic closure of $\mathbb{Q}$. Let $F_0$ be the intermediate field `qExpFunctionFieldC ℚ (Gamma0 M')`, i.e. the subfield of $\mathbb{Q}(\!(X)\!)$ generated over $\mathbb{Q}$ by all quotients of integral $q$-expansion series attached to pairs of modular forms of equal weight for $\Gamma_0(M')$ (denominator series nonzero); let $\overline{F_0}$ be its base change, the subfield of $\overline{\mathbb{Q}}(\!(X)\!)$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of $F_0$. Let $K^\sharp$ be the subfield generated over $\overline{\mathbb{Q}}$ by the image of $\overline{F_0}$ under `qExpand`, the ring endomorphism of $\overline{\mathbb{Q}}(\!(X)\!)$ multiplying all exponents by $q$ (substitution $X \mapsto X^q$). Let $\overline{F}$ be `fieldBar q M'`, the base change to $\overline{\mathbb{Q}}$ of the $X_H$ function field of level $q^2M'$ for the subgroup $H \le (\mathbb{Z}/q^2M')^\times$ which is the kernel of reduction to $(\mathbb{Z}/q)^\times$. The assertion is threefold: $K^\sharp \le \overline{F}$; the relative degree of $\overline{F}$ over $K^\sharp \sqcap \overline{F}$ is strictly positive (hence finite and nonzero); and that relative degree is at most $q(q^2-1) = 6$.
--
--   This is the $q = 2$ case of the comparison between the full-level function field of level $q^2M'$ and the field of level-$\Gamma_0(M')$ functions read in $X^q$; for odd $q$ the corresponding statements carry an extra factor $2$ in the bound, which is absent here because $-I \in \Gamma(2)$, so the relevant index is $|\mathrm{SL}_2(\mathbb{Z}/2)| = 6 = q(q^2-1)$. It is used in the construction of a Laurent series in the full-level field that is a $q$-scaled expansion, namely by [`ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ)))) ≤ fieldBar q M' ∧
    0 < (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M') ∧
    (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M') ≤ q * (q ^ 2 - 1) := by sorry
