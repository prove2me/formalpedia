-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three
-- name    : ModularCurve.FullLevel.adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/8864ae6c-f0cd-5399-abc8-8c5564568efe
-- title:
--   Full-level field over the q-scaled Γ₀(M') field: inclusion and degree bound, q=3
-- statement:
--   Let $q$ be a prime with $q = 3$, and let $M'$ be a nonzero natural number not divisible by $q$. Work inside the Laurent series field over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $F_0 =$ `qExpFunctionFieldC ℚ (Gamma0 M')` be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all quotients $\iota(p_f)/\iota(p_g)$, where $f,g$ are modular forms of a common weight $k$ for $\Gamma_0(M')$ (as a subgroup of $\mathrm{GL}_2(\mathbb{R})$) whose $q$-expansions are the integral power series $p_f,p_g$, with $\iota(p_g)\neq 0$; let $\overline{F_0}$ be the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of $F_0$ under the coefficientwise map induced by $\mathbb{Q}\hookrightarrow\overline{\mathbb{Q}}$. Let $K^\sharp$ be the subfield generated over $\overline{\mathbb{Q}}$ by the image of $\overline{F_0}$ under `qExpand`, the ring homomorphism multiplying all Laurent exponents by $q$ (substitution $q \mapsto q^q$). Finally let $F =$ `fieldBar q M'` be the $\overline{\mathbb{Q}}$-base change, in the same sense, of the intermediate field `xHFunctionField (q ^ 2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. The assertion is threefold: $K^\sharp \subseteq F$; the relative degree of $F$ over $K^\sharp$ is positive (hence finite and nonzero); and $2\,[F:K^\sharp] \le q(q^2-1)$, the bound being stated symbolically in $q$ with natural subtraction.
--
--   This is the $q = 3$ instance of the comparison between the full-level modular function field at level $q^2M'$ (with level structure given by the units congruent to $1$ modulo $q$) and the $\Gamma_0(M')$ function field read in the variable $q^q$, together with the degree bound $2[F:K^\sharp] \le q(q^2-1)$. It feeds the $q = 3$ case of the recognition statement [`ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three), which identifies the Laurent series fixed by the relevant level automorphisms as those of the form `qExpand` applied to a $\Gamma_0$-level function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
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
